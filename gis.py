"""GeoPulse GIS - live street-network and points-of-interest analysis.

A single-file Flask application that builds a real street graph and a real
points-of-interest layer for any place on Earth, using the OpenStreetMap
Overpass API for data and Nominatim for geocoding. All metrics shown to the
user are computed from the returned data (street length, intersection density,
dead-end ratio, road-class mix, POI counts) - nothing is fabricated.

Run locally:
    python gis.py

Serve in production (Windows-friendly), mounted under /gis behind a proxy:
    set GIS_URL_PREFIX=/gis
    waitress-serve --listen=127.0.0.1:5006 gis:app

See README.md for the nginx/Apache reverse-proxy configuration.
"""

from __future__ import annotations

import json
import os
import re
import time
from collections import OrderedDict
from concurrent.futures import ThreadPoolExecutor
from functools import lru_cache
from math import asin, atan2, cos, degrees, log, pi, radians, sin, sqrt
from typing import Any

import networkx as nx
import requests
from flask import Blueprint, Flask, Response, jsonify, request, url_for
from werkzeug.middleware.proxy_fix import ProxyFix

# --------------------------------------------------------------------------- #
# Configuration
# --------------------------------------------------------------------------- #

NETWORK_TYPES = {"drive", "walk", "bike", "all"}
MAX_RADIUS_METERS = 10_000
MIN_RADIUS_METERS = 400
ALL_MODE_MAX_RADIUS = 6_000  # "all paths" is heavy; cap it tighter
MAX_CENTRALITY_NODES = 9_000  # refuse betweenness above this to avoid timeouts
DEFAULT_PLACE = "San Francisco, California"
HTTP_TIMEOUT = 25  # kept under the serverless function wall-clock limit
MAX_POIS = 1500
USER_AGENT = "GeoPulseGIS/2.0 (https://shahzadasghar.org/gis)"
ORIENTATION_BINS = 36  # 10-degree bins for the street-orientation rose

# Typical travel speeds (metres/second) used for routing time and isochrones.
SPEED_MPS = {"drive": 11.1, "bike": 4.2, "walk": 1.4, "all": 1.4}
ACCESS_MINUTES = 15  # the "15-minute neighbourhood" walk window

# Plain-language labels for the everyday-access scorecard.
# Canonical category labels - identical to POI_LABELS so the score card, the
# "what is nearby" toggles, and the map legend all match exactly.
ACCESS_LABELS = {
    "food_retail": "Food & retail",
    "healthcare": "Healthcare",
    "education": "Education",
    "transit": "Transit & fuel",
    "civic": "Civic & finance",
    "leisure": "Parks & leisure",
}

# "Ask the City" - the LLM is grounded strictly on the computed fact sheet.
ASK_MODEL = os.environ.get("GIS_ASK_MODEL", "claude-opus-4-8")
# Abuse controls for the (paid) LLM endpoint. Per-warm-instance, so a spend cap
# on the Anthropic key remains the airtight backstop; these cut casual abuse.
ASK_RATE_LIMIT = int(os.environ.get("GIS_ASK_RATE_LIMIT", "8"))   # requests
ASK_RATE_WINDOW = int(os.environ.get("GIS_ASK_RATE_WINDOW", "60"))  # ...per seconds
ASK_CACHE_MAX = 256                                                 # in-memory entries
ASK_CACHE_TTL = int(os.environ.get("GIS_ASK_CACHE_TTL", "86400"))  # shared-cache seconds

# Optional Upstash Redis (REST) for cross-instance rate limiting + answer cache.
# Accepts Upstash's own var names or Vercel KV's (which is Upstash-backed).
UPSTASH_URL = (os.environ.get("UPSTASH_REDIS_REST_URL")
               or os.environ.get("KV_REST_API_URL") or "").rstrip("/")
UPSTASH_TOKEN = (os.environ.get("UPSTASH_REDIS_REST_TOKEN")
                 or os.environ.get("KV_REST_API_TOKEN") or "")
UPSTASH_ENABLED = bool(UPSTASH_URL and UPSTASH_TOKEN)
ASK_SYSTEM = (
    "You are a city analyst for GeoPulse GIS. Answer the user's question about a "
    "place using ONLY the JSON facts in the user message. Those facts were computed "
    "from live OpenStreetMap data.\n"
    "Rules:\n"
    "- Use only the numbers and categories in the JSON. Never invent places, street "
    "names, neighbourhoods, distances, prices, or statistics that are not present.\n"
    "- If the facts do not contain enough to answer, say so plainly and suggest what "
    "to analyse instead (a different travel mode or radius).\n"
    "- Be concise and plain-spoken for a non-expert. Lead with a one-sentence "
    "direct answer, then add detail.\n"
    "- Format as clean Markdown. When listing things, use a bullet list with each "
    "item on its own line starting with '- ', like '- **Healthcare:** 31 (nearest "
    "7 min)'. Put a blank line before the list. Keep it tight (no more than ~6 bullets).\n"
    "- Cite the relevant numbers (e.g. 'walkability 82/100', '12 groceries & dining "
    "within a 15-minute walk').\n"
    "- Do not output your reasoning or preamble, and do not say 'based on the data'. "
    "Give only the answer.\n"
    "- Walkability and counts are estimates from mapped data, not a survey; do not "
    "overstate certainty."
)

OVERPASS_ENDPOINTS = [
    endpoint
    for endpoint in [
        os.environ.get("GIS_OVERPASS_URL"),
        "https://overpass-api.de/api/interpreter",
        "https://overpass.kumi.systems/api/interpreter",
        "https://maps.mail.ru/osm/tools/overpass/api/interpreter",
    ]
    if endpoint
]
NOMINATIM_URL = os.environ.get(
    "GIS_NOMINATIM_URL", "https://nominatim.openstreetmap.org"
)

# Overpass "highway" filters per travel mode (positive whitelists).
HIGHWAY_FILTERS = {
    "drive": (
        "motorway|motorway_link|trunk|trunk_link|primary|primary_link|"
        "secondary|secondary_link|tertiary|tertiary_link|unclassified|"
        "residential|living_street|service|road"
    ),
    "walk": (
        "footway|path|pedestrian|steps|living_street|residential|unclassified|"
        "tertiary|tertiary_link|secondary|secondary_link|primary|primary_link|"
        "service|track|cycleway|road"
    ),
    "bike": (
        "cycleway|residential|living_street|tertiary|tertiary_link|secondary|"
        "secondary_link|primary|primary_link|unclassified|path|service|track|"
        "footway|road"
    ),
    "all": (
        "motorway|motorway_link|trunk|trunk_link|primary|primary_link|"
        "secondary|secondary_link|tertiary|tertiary_link|unclassified|"
        "residential|living_street|service|footway|path|pedestrian|steps|"
        "cycleway|track|road"
    ),
}

# Map a raw OSM tag value to a human POI category. Checked in this order.
POI_CATEGORIES = {
    "healthcare": {"hospital", "clinic", "doctors", "pharmacy", "dentist"},
    "education": {"school", "university", "college", "kindergarten", "library"},
    "food_retail": {
        "restaurant",
        "cafe",
        "fast_food",
        "bar",
        "marketplace",
        "supermarket",
        "convenience",
        "mall",
        "department_store",
    },
    "transit": {
        "bus_station",
        "bus_stop",
        "station",
        "subway_entrance",
        "tram_stop",
        "halt",
        "platform",
        "stop_position",
        "fuel",
    },
    "civic": {
        "police",
        "fire_station",
        "townhall",
        "courthouse",
        "post_office",
        "bank",
        "atm",
    },
    "leisure": {"park", "garden", "playground", "pitch", "sports_centre"},
}
POI_LABELS = {
    "healthcare": "Healthcare",
    "education": "Education",
    "food_retail": "Food & retail",
    "transit": "Transit & fuel",
    "civic": "Civic & finance",
    "leisure": "Parks & leisure",
}

# Offline coordinates so the built-in demo cities resolve without a geocoder.
FALLBACK_LOCATIONS = {
    "amman, jordan": (31.9539, 35.9106),
    "amman": (31.9539, 35.9106),
    "jordan": (31.9539, 35.9106),
    "dubai, united arab emirates": (25.2048, 55.2708),
    "dubai": (25.2048, 55.2708),
    "san francisco, california": (37.7749, -122.4194),
    "san francisco": (37.7749, -122.4194),
    "tokyo, japan": (35.6762, 139.6503),
    "tokyo": (35.6762, 139.6503),
    "riyadh, saudi arabia": (24.7136, 46.6753),
    "riyadh": (24.7136, 46.6753),
    "doha, qatar": (25.2854, 51.5310),
    "doha": (25.2854, 51.5310),
    "london, united kingdom": (51.5072, -0.1276),
    "london": (51.5072, -0.1276),
    "new york, united states": (40.7128, -74.0060),
    "new york": (40.7128, -74.0060),
}

_session = requests.Session()
_session.headers.update({"User-Agent": USER_AGENT})


# --------------------------------------------------------------------------- #
# Geometry helpers
# --------------------------------------------------------------------------- #


def haversine_m(lat1: float, lon1: float, lat2: float, lon2: float) -> float:
    """Great-circle distance between two points, in metres."""
    r = 6_371_000.0
    d_lat = radians(lat2 - lat1)
    d_lon = radians(lon2 - lon1)
    a = (
        sin(d_lat / 2) ** 2
        + cos(radians(lat1)) * cos(radians(lat2)) * sin(d_lon / 2) ** 2
    )
    return 2 * r * asin(sqrt(min(1.0, a)))


def polygon_area_m2(points: list[tuple[float, float]]) -> float:
    """Approximate geodesic area of a small polygon (lat, lon points), m^2."""
    if len(points) < 3:
        return 0.0
    r = 6_371_000.0
    total = 0.0
    n = len(points)
    for i in range(n):
        lat1, lon1 = points[i]
        lat2, lon2 = points[(i + 1) % n]
        total += radians(lon2 - lon1) * (
            2 + sin(radians(lat1)) + sin(radians(lat2))
        )
    return abs(total * r * r / 2.0)


def bearing_deg(lat1: float, lon1: float, lat2: float, lon2: float) -> float:
    """Compass bearing from point 1 to point 2, in degrees [0, 360)."""
    d_lon = radians(lon2 - lon1)
    y = sin(d_lon) * cos(radians(lat2))
    x = cos(radians(lat1)) * sin(radians(lat2)) - sin(radians(lat1)) * cos(
        radians(lat2)
    ) * cos(d_lon)
    return (degrees(atan2(y, x)) + 360) % 360


def orientation_summary(bins: list[float]) -> dict[str, Any]:
    """Normalise an orientation histogram and derive a grid-order index."""
    total = sum(bins) or 1.0
    fractions = [value / total for value in bins]
    entropy = -sum(p * log(p) for p in fractions if p > 0)
    max_entropy = log(len(bins)) if len(bins) > 1 else 1.0
    # 0 = fully dispersed orientations, 100 = a single dominant grid direction.
    order = round((1 - entropy / max_entropy) * 100) if max_entropy else 0
    return {
        "bins": [round(value, 4) for value in fractions],
        "bin_count": len(bins),
        "order": max(0, min(100, order)),
        "entropy": round(entropy / max_entropy, 3) if max_entropy else 0.0,
    }


def nearest_node(nodes: dict[int, tuple[float, float]], lat: float,
                 lon: float) -> int | None:
    """Return the id of the graph node closest to (lat, lon)."""
    best_id, best_dist = None, float("inf")
    for node_id, (node_lat, node_lon) in nodes.items():
        # Cheap squared-degree distance is enough to pick the nearest node.
        dist = (node_lat - lat) ** 2 + (node_lon - lon) ** 2
        if dist < best_dist:
            best_dist, best_id = dist, node_id
    return best_id


def convex_hull(points: list[tuple[float, float]]) -> list[list[float]]:
    """Andrew's monotone chain hull. Input/-output are [lon, lat] points."""
    pts = sorted(set((round(x, 6), round(y, 6)) for x, y in points))
    if len(pts) < 3:
        return [[x, y] for x, y in pts]

    def cross(o, a, b):
        return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])

    lower: list[tuple[float, float]] = []
    for p in pts:
        while len(lower) >= 2 and cross(lower[-2], lower[-1], p) <= 0:
            lower.pop()
        lower.append(p)
    upper: list[tuple[float, float]] = []
    for p in reversed(pts):
        while len(upper) >= 2 and cross(upper[-2], upper[-1], p) <= 0:
            upper.pop()
        upper.append(p)
    hull = lower[:-1] + upper[:-1]
    return [[x, y] for x, y in hull]


def parse_latlon(text: str) -> tuple[float, float] | None:
    """Return (lat, lon) if the text looks like a coordinate pair."""
    match = re.fullmatch(
        r"\s*(-?\d+(?:\.\d+)?)\s*,\s*(-?\d+(?:\.\d+)?)\s*", text or ""
    )
    if not match:
        return None
    lat, lon = float(match.group(1)), float(match.group(2))
    if -90 <= lat <= 90 and -180 <= lon <= 180:
        return lat, lon
    return None


# --------------------------------------------------------------------------- #
# OpenStreetMap access
# --------------------------------------------------------------------------- #


def overpass_query(query: str) -> dict[str, Any]:
    """Run an Overpass QL query, trying each configured mirror in turn."""
    last_error: Exception | None = None
    for endpoint in OVERPASS_ENDPOINTS:
        try:
            response = _session.post(
                endpoint, data={"data": query}, timeout=HTTP_TIMEOUT
            )
            if response.status_code in (429, 504):
                last_error = RuntimeError(
                    f"{endpoint} is busy (HTTP {response.status_code})."
                )
                continue
            response.raise_for_status()
            return response.json()
        except Exception as exc:  # noqa: BLE001 - try the next mirror
            last_error = exc
            continue
    raise RuntimeError(
        f"All Overpass endpoints failed. Last error: {last_error}"
    )


def short_place(display_name: str) -> str:
    """Trim a long Nominatim display name to 'City, Country'."""
    parts = [p.strip() for p in display_name.split(",") if p.strip()]
    if len(parts) <= 2:
        return display_name.strip()
    return f"{parts[0]}, {parts[-1]}"


@lru_cache(maxsize=256)
def geocode_place(place: str) -> tuple[float, float, str]:
    """Resolve a place name (or 'lat,lon') to (lat, lon, short_label)."""
    coords = parse_latlon(place)
    if coords:
        lat, lon = coords
        return lat, lon, f"{lat:.4f}, {lon:.4f}"

    fallback = FALLBACK_LOCATIONS.get(place.strip().lower())

    try:
        response = _session.get(
            f"{NOMINATIM_URL}/search",
            params={
                "q": place,
                "format": "jsonv2",
                "limit": 1,
                "accept-language": "en",  # keep labels in English
            },
            timeout=HTTP_TIMEOUT,
        )
        response.raise_for_status()
        results = response.json()
        if results:
            top = results[0]
            return (
                float(top["lat"]),
                float(top["lon"]),
                short_place(top.get("display_name", place)),
            )
    except Exception:  # noqa: BLE001 - fall back to the offline table
        pass

    if fallback:
        return fallback[0], fallback[1], place.strip()
    raise RuntimeError(
        f"Could not find '{place}'. Try a more specific name or 'lat, lon'."
    )


def fetch_streets(lat: float, lon: float, radius_m: int, network_type: str) -> dict:
    regex = HIGHWAY_FILTERS[network_type]
    query = (
        f"[out:json][timeout:{HTTP_TIMEOUT}];"
        f'way(around:{radius_m},{lat},{lon})["highway"~"^({regex})$"]'
        f'["area"!~"yes"];'
        f"out geom;"
    )
    return overpass_query(query)


def fetch_pois(lat: float, lon: float, radius_m: int) -> dict:
    selectors = (
        f'nwr(around:{radius_m},{lat},{lon})["amenity"~"^(hospital|clinic|'
        f"doctors|pharmacy|dentist|school|university|college|kindergarten|"
        f"library|restaurant|cafe|fast_food|bar|bank|atm|police|fire_station|"
        f'townhall|courthouse|post_office|marketplace|bus_station|fuel)$"];'
        f'nwr(around:{radius_m},{lat},{lon})["shop"~"^(supermarket|convenience|'
        f'mall|department_store)$"];'
        f'nwr(around:{radius_m},{lat},{lon})["railway"~"^(station|'
        f'subway_entrance|tram_stop|halt)$"];'
        f'nwr(around:{radius_m},{lat},{lon})["public_transport"~"^(station|'
        f'platform|stop_position)$"];'
        f'nwr(around:{radius_m},{lat},{lon})["highway"="bus_stop"];'
        f'nwr(around:{radius_m},{lat},{lon})["leisure"~"^(park|garden|'
        f'playground|pitch|sports_centre)$"];'
    )
    query = f"[out:json][timeout:{HTTP_TIMEOUT}];({selectors});out center 2000;"
    return overpass_query(query)


# --------------------------------------------------------------------------- #
# Parsing and metrics
# --------------------------------------------------------------------------- #


def road_class(tags: dict[str, Any]) -> str:
    value = tags.get("highway", "unclassified")
    if isinstance(value, list) and value:
        value = value[0]
    return str(value).split(";")[0] if value else "unclassified"


def build_street_network(raw: dict, place: str, lat: float, lon: float,
                         radius_m: int, network_type: str,
                         source: str) -> dict[str, Any]:
    """Turn raw Overpass ways into GeoJSON plus computed graph metrics."""
    features: list[dict[str, Any]] = []
    graph = nx.Graph()
    node_coords: dict[int, tuple[float, float]] = {}
    orientation = [0.0] * ORIENTATION_BINS
    bin_size = 360 / ORIENTATION_BINS
    road_mix: dict[str, int] = {}
    total_length_m = 0.0
    straight_length_m = 0.0
    min_lat = min_lon = float("inf")
    max_lat = max_lon = float("-inf")

    for element in raw.get("elements", []):
        if element.get("type") != "way":
            continue
        geometry = element.get("geometry") or []
        nodes = element.get("nodes") or []
        if len(geometry) < 2:
            continue

        coords = [
            [round(point["lon"], 6), round(point["lat"], 6)] for point in geometry
        ]
        tags = element.get("tags", {})
        klass = road_class(tags)

        way_length = 0.0
        for (a, b) in zip(geometry, geometry[1:]):
            seg = haversine_m(a["lat"], a["lon"], b["lat"], b["lon"])
            way_length += seg
            # Orientation rose: bin both directions of each segment by length.
            brng = bearing_deg(a["lat"], a["lon"], b["lat"], b["lon"])
            orientation[int(brng // bin_size) % ORIENTATION_BINS] += seg
            orientation[int(((brng + 180) % 360) // bin_size) % ORIENTATION_BINS] += seg
        if way_length <= 0:
            continue

        # Build a weighted topology graph for connectivity, routing, isochrones.
        usable = min(len(nodes), len(geometry))
        for i in range(usable):
            node_coords[nodes[i]] = (geometry[i]["lat"], geometry[i]["lon"])
        for i in range(usable - 1):
            a, b = geometry[i], geometry[i + 1]
            graph.add_edge(
                nodes[i], nodes[i + 1],
                length=haversine_m(a["lat"], a["lon"], b["lat"], b["lon"]),
            )
        if not nodes:
            graph.add_node(id(element))

        straight_length_m += haversine_m(
            geometry[0]["lat"], geometry[0]["lon"],
            geometry[-1]["lat"], geometry[-1]["lon"],
        )
        total_length_m += way_length
        road_mix[klass] = road_mix.get(klass, 0) + 1

        for lonlat in coords:
            min_lon, max_lon = min(min_lon, lonlat[0]), max(max_lon, lonlat[0])
            min_lat, max_lat = min(min_lat, lonlat[1]), max(max_lat, lonlat[1])

        features.append(
            {
                "type": "Feature",
                "properties": {
                    "name": tags.get("name", "Unnamed street"),
                    "highway": klass,
                    "length": round(way_length, 1),
                },
                "geometry": {"type": "LineString", "coordinates": coords},
            }
        )

    if not features:
        raise RuntimeError(
            f"No {network_type} streets were returned for {place}. "
            "Try a larger radius or a different travel mode."
        )

    degrees = dict(graph.degree())
    intersections = sum(1 for value in degrees.values() if value >= 3)
    dead_ends = sum(1 for value in degrees.values() if value == 1)
    node_count = graph.number_of_nodes()

    area_sqkm = pi * (radius_m / 1000) ** 2
    total_km = total_length_m / 1000
    km_per_sqkm = total_km / area_sqkm if area_sqkm else 0.0
    intersection_density = intersections / area_sqkm if area_sqkm else 0.0
    dead_end_ratio = dead_ends / max(intersections + dead_ends, 1)
    circuity = total_length_m / straight_length_m if straight_length_m else 1.0
    avg_segment_m = total_length_m / len(features)

    # Connectivity index: a transparent 0-100 blend of intersection density
    # and street continuity. It is a derived heuristic, not a measured value.
    connectivity_index = int(
        max(
            0,
            min(
                100,
                round(
                    0.6 * min(intersection_density / 1.5, 100)
                    + 0.4 * (1 - dead_end_ratio) * 100
                ),
            ),
        )
    )

    mix_items = [
        {"type": key, "count": count}
        for key, count in sorted(
            road_mix.items(), key=lambda item: item[1], reverse=True
        )
    ]

    bounds = [[min_lat, min_lon], [max_lat, max_lon]]
    rose = orientation_summary(orientation)

    return {
        "geojson": {"type": "FeatureCollection", "features": features},
        "center": [lat, lon],
        "bounds": bounds,
        "orientation": rose,
        "_graph": graph,
        "_nodes": node_coords,
        "stats": {
            "place": place,
            "network_type": network_type,
            "radius_m": radius_m,
            "nodes": node_count,
            "edges": len(features),
            "intersections": intersections,
            "dead_ends": dead_ends,
            "total_km": round(total_km, 2),
            "km_per_sqkm": round(km_per_sqkm, 2),
            "intersection_density": round(intersection_density, 1),
            "dead_end_ratio": round(dead_end_ratio, 3),
            "circuity": round(circuity, 3),
            "avg_segment_m": round(avg_segment_m, 1),
            "connectivity_index": connectivity_index,
            "grid_order": rose["order"],
            "road_mix": mix_items,
            "source": source,
        },
    }


def classify_poi(tags: dict[str, Any]) -> str | None:
    candidates = [
        tags.get("amenity"),
        tags.get("shop"),
        tags.get("railway"),
        tags.get("public_transport"),
        tags.get("leisure"),
        "bus_stop" if tags.get("highway") == "bus_stop" else None,
    ]
    for value in candidates:
        if not value:
            continue
        for category, members in POI_CATEGORIES.items():
            if value in members:
                return category
    return None


def build_pois(raw: dict) -> dict[str, Any]:
    """Group Overpass POI elements into categories of GeoJSON points."""
    groups: dict[str, list[dict[str, Any]]] = {key: [] for key in POI_CATEGORIES}
    total = 0

    for element in raw.get("elements", []):
        tags = element.get("tags", {})
        category = classify_poi(tags)
        if not category:
            continue

        if element.get("type") == "node":
            lat, lon = element.get("lat"), element.get("lon")
        else:
            center = element.get("center") or {}
            lat, lon = center.get("lat"), center.get("lon")
        if lat is None or lon is None:
            continue

        total += 1
        if total > MAX_POIS:
            continue

        groups[category].append(
            {
                "type": "Feature",
                "properties": {
                    "name": tags.get("name", POI_LABELS[category]),
                    "category": category,
                    "kind": (
                        tags.get("amenity")
                        or tags.get("shop")
                        or tags.get("railway")
                        or tags.get("leisure")
                        or tags.get("public_transport")
                        or "point"
                    ),
                },
                "geometry": {
                    "type": "Point",
                    "coordinates": [round(lon, 6), round(lat, 6)],
                },
            }
        )

    categories = {
        key: {
            "label": POI_LABELS[key],
            "count": len(features),
            "geojson": {"type": "FeatureCollection", "features": features},
        }
        for key, features in groups.items()
    }
    return {
        "categories": categories,
        "total": total,
        "shown": min(total, MAX_POIS),
        "capped": total > MAX_POIS,
    }


def build_insights(stats: dict[str, Any], pois: dict[str, Any]) -> list[dict[str, str]]:
    """Honest, data-derived observations - no fabricated claims."""
    insights: list[dict[str, str]] = []

    dominant = stats["road_mix"][0]["type"] if stats["road_mix"] else "local"
    order = stats.get("grid_order", 0)
    grid_phrase = (
        "a strong single-grid orientation" if order >= 55
        else "a semi-gridded layout" if order >= 30
        else "an organic, multi-directional layout"
    )
    insights.append(
        {
            "title": "Network composition",
            "detail": (
                f"{stats['edges']} street segments totalling "
                f"{stats['total_km']} km, most commonly classed as "
                f"'{dominant}'. Street density is {stats['km_per_sqkm']} km "
                f"per square kilometre, with {grid_phrase} "
                f"(grid-order {order}/100)."
            ),
        }
    )

    ratio_pct = round(stats["dead_end_ratio"] * 100)
    if ratio_pct <= 12:
        grid = "well-connected grid with few dead-ends"
    elif ratio_pct <= 25:
        grid = "moderately connected layout"
    else:
        grid = "low-connectivity layout with many dead-ends"
    insights.append(
        {
            "title": "Connectivity",
            "detail": (
                f"{stats['intersections']} intersections "
                f"({stats['intersection_density']} per km2) and "
                f"{ratio_pct}% dead-end nodes indicate a {grid}. "
                f"Average circuity is {stats['circuity']} "
                f"(1.0 = perfectly straight)."
            ),
        }
    )

    ordered = sorted(
        pois["categories"].items(), key=lambda kv: kv[1]["count"], reverse=True
    )
    top = [f"{value['count']} {value['label'].lower()}" for _, value in ordered[:3] if value["count"]]
    if top:
        insights.append(
            {
                "title": "Services nearby",
                "detail": (
                    f"{pois['total']} mapped points of interest in range, led by "
                    + ", ".join(top)
                    + ". Toggle the layers to inspect each category."
                ),
            }
        )
    else:
        insights.append(
            {
                "title": "Services nearby",
                "detail": "No tagged points of interest were returned for this area.",
            }
        )

    return insights


# --------------------------------------------------------------------------- #
# Graph analytics: routing, isochrones, centrality
# --------------------------------------------------------------------------- #


def compute_route(graph: nx.Graph, nodes: dict[int, tuple[float, float]],
                  origin: tuple[float, float], dest: tuple[float, float],
                  speed_mps: float) -> dict[str, Any]:
    src = nearest_node(nodes, origin[0], origin[1])
    dst = nearest_node(nodes, dest[0], dest[1])
    if src is None or dst is None:
        raise RuntimeError("No routable nodes near those points.")
    try:
        path = nx.shortest_path(graph, src, dst, weight="length")
    except nx.NetworkXNoPath:
        raise RuntimeError("No connected route exists between those points.")

    coordinates = [[nodes[n][1], nodes[n][0]] for n in path]
    distance_m = sum(
        graph[path[i]][path[i + 1]]["length"] for i in range(len(path) - 1)
    )
    return {
        "type": "Feature",
        "properties": {
            "distance_m": round(distance_m, 1),
            "distance_km": round(distance_m / 1000, 2),
            "time_min": round(distance_m / speed_mps / 60, 1),
            "stops": len(path),
        },
        "geometry": {"type": "LineString", "coordinates": coordinates},
    }


def compute_isochrone(graph: nx.Graph, nodes: dict[int, tuple[float, float]],
                      origin: tuple[float, float], minutes: float,
                      speed_mps: float) -> dict[str, Any]:
    src = nearest_node(nodes, origin[0], origin[1])
    if src is None:
        raise RuntimeError("No routable nodes near that point.")
    budget_m = minutes * 60 * speed_mps
    lengths = nx.single_source_dijkstra_path_length(
        graph, src, cutoff=budget_m, weight="length"
    )
    reachable = set(lengths)

    edges: list[dict[str, Any]] = []
    reachable_m = 0.0
    for u, v, data in graph.edges(data=True):
        if u in reachable and v in reachable:
            reachable_m += data["length"]
            if len(edges) < 6000:
                edges.append(
                    {
                        "type": "Feature",
                        "properties": {},
                        "geometry": {
                            "type": "LineString",
                            "coordinates": [
                                [nodes[u][1], nodes[u][0]],
                                [nodes[v][1], nodes[v][0]],
                            ],
                        },
                    }
                )

    hull_points = [[nodes[n][1], nodes[n][0]] for n in reachable]
    hull = convex_hull([(p[0], p[1]) for p in hull_points])
    hull_feature = None
    if len(hull) >= 3:
        hull_feature = {
            "type": "Feature",
            "properties": {},
            "geometry": {"type": "Polygon", "coordinates": [hull + [hull[0]]]},
        }

    return {
        "edges": {"type": "FeatureCollection", "features": edges},
        "hull": hull_feature,
        "stats": {
            "minutes": minutes,
            "reachable_nodes": len(reachable),
            "reachable_km": round(reachable_m / 1000, 2),
            "speed_kmh": round(speed_mps * 3.6, 1),
        },
    }


def compute_centrality(graph: nx.Graph, nodes: dict[int, tuple[float, float]],
                       top_fraction: float = 0.2) -> dict[str, Any]:
    """Edge betweenness centrality: which streets carry the most paths."""
    n = graph.number_of_nodes()
    if n < 2:
        return {"type": "FeatureCollection", "features": []}
    if n > MAX_CENTRALITY_NODES:
        raise RuntimeError(
            "This area is too large for corridor analysis. Reduce the radius and try again."
        )
    k = None if n <= 250 else min(160, n - 1)
    scores = nx.edge_betweenness_centrality(
        graph, k=k, weight="length", seed=42
    )
    if not scores:
        return {"type": "FeatureCollection", "features": []}

    ordered = sorted(scores.values(), reverse=True)
    cutoff = ordered[min(len(ordered) - 1, int(len(ordered) * top_fraction))]
    peak = ordered[0] or 1.0

    features = []
    for (u, v), value in scores.items():
        if value < cutoff:
            continue
        features.append(
            {
                "type": "Feature",
                "properties": {"score": round(value / peak, 4)},
                "geometry": {
                    "type": "LineString",
                    "coordinates": [
                        [nodes[u][1], nodes[u][0]],
                        [nodes[v][1], nodes[v][0]],
                    ],
                },
            }
        )
    return {"type": "FeatureCollection", "features": features, "sampled": k is not None}


# --------------------------------------------------------------------------- #
# Everyday access: the "15-minute neighbourhood" analysis for non-experts
# --------------------------------------------------------------------------- #


def build_node_grid(nodes: dict[int, tuple[float, float]], cell: float = 0.003):
    """Coarse spatial buckets so points snap to a nearby node quickly."""
    grid: dict[tuple[int, int], list[int]] = {}
    for node_id, (lat, lon) in nodes.items():
        grid.setdefault((round(lat / cell), round(lon / cell)), []).append(node_id)
    return grid, cell


def snap_to_node(grid, cell, nodes, lat: float, lon: float) -> int | None:
    kx, ky = round(lat / cell), round(lon / cell)
    best, best_d = None, float("inf")
    for dx in (-1, 0, 1):
        for dy in (-1, 0, 1):
            for node_id in grid.get((kx + dx, ky + dy), []):
                nlat, nlon = nodes[node_id]
                d = (nlat - lat) ** 2 + (nlon - lon) ** 2
                if d < best_d:
                    best_d, best = d, node_id
    return best if best is not None else nearest_node(nodes, lat, lon)


def compute_access(graph: nx.Graph, nodes: dict[int, tuple[float, float]],
                   poi_categories: dict[str, Any], center: list[float],
                   minutes: int = ACCESS_MINUTES) -> dict[str, Any] | None:
    """How much of daily life is reachable on foot from the centre.

    Walk distance is measured along the mapped street graph (Dijkstra), so the
    counts and 'nearest' times are real, not straight-line guesses.
    """
    if not nodes or graph.number_of_nodes() == 0:
        return None
    speed = SPEED_MPS["walk"]
    budget = minutes * 60 * speed

    center_node = nearest_node(nodes, center[0], center[1])
    if center_node is None:
        return None
    # Cutoff at the walk budget so Dijkstra stops early; POIs beyond it fall
    # back to straight-line distance (they read as "none within N min" anyway).
    dist = nx.single_source_dijkstra_path_length(
        graph, center_node, cutoff=budget, weight="length"
    )
    grid, cell = build_node_grid(nodes)

    categories: list[dict[str, Any]] = []
    total_reachable = 0
    for key, info in poi_categories.items():
        count = 0
        nearest_m: float | None = None
        for feature in info["geojson"]["features"]:
            lon, lat = feature["geometry"]["coordinates"]
            node_id = snap_to_node(grid, cell, nodes, lat, lon)
            d = dist.get(node_id)
            if d is None:
                continue  # not reachable on foot within the time budget
            count += 1
            if nearest_m is None or d < nearest_m:
                nearest_m = d
        total_reachable += count
        categories.append({
            "key": key,
            "label": ACCESS_LABELS.get(key, info["label"]),
            "count": count,
            "present": count > 0,
            "nearest_m": round(nearest_m) if nearest_m is not None else None,
            "nearest_min": (round(nearest_m / speed / 60, 1)
                            if nearest_m is not None else None),
        })

    present_cats = [c for c in categories if c["present"]]
    present = len(present_cats)
    total_cats = len(categories) or 1
    # Three transparent, explainable factors, capped at 99 (never a suspicious 100).
    coverage = present / total_cats                      # how many of the categories
    abundance = min(1.0, total_reachable / 80.0)         # how many places overall
    # Proximity averaged over ALL categories (absent count as 0) so the score is
    # monotonic: adding an amenity can only raise it, closing streets only lower it.
    proximity = sum(
        max(0.0, 1 - c["nearest_min"] / minutes) for c in present_cats
    ) / total_cats
    score = int(round(100 * (0.5 * coverage + 0.25 * abundance + 0.25 * proximity)))
    score = max(0, min(99, score))
    factors = {
        "coverage": round(coverage, 2),
        "abundance": round(abundance, 2),
        "proximity": round(proximity, 2),
    }
    method = ("Score blends category coverage (50%), number of places (25%), "
              "and how close they are (25%), within a 15-minute walk.")

    if score >= 80:
        verdict = "Highly walkable. Most daily needs are a short walk away."
    elif score >= 60:
        verdict = "Walkable. Many everyday services are within reach on foot."
    elif score >= 40:
        verdict = "Somewhat walkable. Some services are near; expect to travel for others."
    else:
        verdict = "Car-dependent. Few services are within a comfortable walk."

    top = sorted((c for c in categories if c["count"]),
                 key=lambda c: c["count"], reverse=True)[:3]
    if top:
        summary = (f"Within a {minutes}-minute walk: "
                   + ", ".join(f"{c['count']} {c['label'].lower()}" for c in top) + ".")
    else:
        summary = f"No everyday services were found within a {minutes}-minute walk."

    reachable_pts = [(nodes[n][1], nodes[n][0]) for n in dist]
    hull = convex_hull(reachable_pts)
    zone = None
    if len(hull) >= 3:
        zone = {
            "type": "Feature",
            "properties": {"minutes": minutes},
            "geometry": {"type": "Polygon", "coordinates": [hull + [hull[0]]]},
        }

    return {
        "minutes": minutes,
        "score": score,
        "verdict": verdict,
        "summary": summary,
        "total_reachable": total_reachable,
        "categories": categories,
        "factors": factors,
        "method": method,
        "zone": zone,
    }


# --------------------------------------------------------------------------- #
# What-If Studio: edit the network/amenities and recompute the impact
# --------------------------------------------------------------------------- #


def apply_whatif(base: dict[str, Any], interventions: list[dict[str, Any]],
                 max_iv: int = 25) -> dict[str, Any]:
    """Apply proposed changes to a copy of the cached graph and re-score.

    Supported interventions:
      - {"type": "add", "category": <key>, "lat": .., "lon": ..} - add an amenity
      - {"type": "close", "lat": .., "lon": .., "radius": m} - close streets nearby
    The base graph is never mutated; everything runs on a copy.
    """
    graph = base["_graph"].copy()
    nodes = base["_nodes"]  # coordinates are read-only here
    poi_cats: dict[str, Any] = {}
    for key, info in base["pois"]["categories"].items():
        poi_cats[key] = {
            "label": info["label"],
            "count": info["count"],
            "geojson": {"type": "FeatureCollection",
                        "features": list(info["geojson"]["features"])},
        }
    center = base["center"]
    removed: list[dict[str, Any]] = []
    added: list[dict[str, Any]] = []

    for iv in (interventions or [])[:max_iv]:
        kind = iv.get("type")
        if kind == "add":
            cat = iv.get("category")
            if cat in poi_cats:
                lat, lon = float(iv["lat"]), float(iv["lon"])
                poi_cats[cat]["geojson"]["features"].append({
                    "type": "Feature",
                    "properties": {"name": "Proposed " + poi_cats[cat]["label"],
                                   "category": cat, "kind": "proposed"},
                    "geometry": {"type": "Point",
                                 "coordinates": [round(lon, 6), round(lat, 6)]},
                })
                added.append({"lat": lat, "lon": lon, "category": cat})
        elif kind == "close":
            lat, lon = float(iv["lat"]), float(iv["lon"])
            radius = min(float(iv.get("radius", 150)), 600)
            drop = []
            for u, v in graph.edges():
                a, b = nodes.get(u), nodes.get(v)
                if not a or not b:
                    continue
                if haversine_m(lat, lon, (a[0] + b[0]) / 2, (a[1] + b[1]) / 2) <= radius:
                    drop.append((u, v))
            graph.remove_edges_from(drop)
            for (u, v) in drop:
                a, b = nodes[u], nodes[v]
                removed.append({
                    "type": "Feature", "properties": {},
                    "geometry": {"type": "LineString",
                                 "coordinates": [[a[1], a[0]], [b[1], b[0]]]},
                })

    new_access = compute_access(graph, nodes, poi_cats, center)
    base_access = base.get("access")
    delta = None
    if base_access and new_access:
        base_by = {c["key"]: c for c in base_access["categories"]}
        cats = []
        for c in new_access["categories"]:
            before = base_by.get(c["key"], {}).get("count", 0)
            cats.append({"key": c["key"], "label": c["label"],
                         "before": before, "after": c["count"],
                         "delta": c["count"] - before})
        delta = {
            "score_before": base_access["score"],
            "score_after": new_access["score"],
            "score_delta": new_access["score"] - base_access["score"],
            "categories": cats,
        }

    return {
        "new_access": new_access,
        "delta": delta,
        "removed_edges": {"type": "FeatureCollection", "features": removed},
        "added": added,
    }


def build_fact_sheet(result: dict[str, Any]) -> dict[str, Any]:
    """A compact, grounded summary the LLM narrates - real numbers only."""
    stats = result["stats"]
    access = result.get("access") or {}
    pois = result.get("pois") or {}
    access_cats = [
        {"category": c["label"], "within_15min_walk": c["count"],
         "nearest_walk_min": c["nearest_min"]}
        for c in (access.get("categories") or [])
    ]
    return {
        "place": stats["place"],
        "travel_mode": stats["network_type"],
        "analysis_radius_m": stats["radius_m"],
        "walkability_score_0_100": access.get("score"),
        "walkability_verdict": access.get("verdict"),
        "street_segments": stats["edges"],
        "intersections": stats["intersections"],
        "total_street_km": stats["total_km"],
        "street_density_km_per_km2": stats["km_per_sqkm"],
        "grid_order_0_100": stats.get("grid_order"),
        "dead_end_ratio": stats.get("dead_end_ratio"),
        "avg_segment_m": stats.get("avg_segment_m"),
        "points_of_interest_total": pois.get("total"),
        "everyday_access_within_15min_walk": access_cats,
        "data_source": stats.get("source"),
    }


# --------------------------------------------------------------------------- #
# Demo fallback (clearly labelled - used only when Overpass is unreachable)
# --------------------------------------------------------------------------- #


def meters_to_degrees(lat: float, north_m: float, east_m: float) -> tuple[float, float]:
    lat_delta = north_m / 111_320
    lon_delta = east_m / (111_320 * max(cos(radians(lat)), 0.2))
    return lat_delta, lon_delta


def build_demo_network(place: str, network_type: str, radius_m: int,
                       lat: float, lon: float) -> dict[str, Any]:
    """A small synthetic grid, returned only when live data is unavailable."""
    features: list[dict[str, Any]] = []
    road_mix = {"primary": 0, "secondary": 0, "residential": 0}
    total_length_m = 0.0
    spacing = max(260, radius_m // 8)
    limit = radius_m * 0.86
    offsets = list(range(-int(limit), int(limit) + 1, spacing))

    for index, offset in enumerate(offsets):
        road = "primary" if index == len(offsets) // 2 else (
            "secondary" if index % 3 == 0 else "residential"
        )
        for vertical in (True, False):
            if vertical:
                d_lat_a, d_lon_a = meters_to_degrees(lat, -limit, offset)
                d_lat_b, d_lon_b = meters_to_degrees(lat, limit, offset)
            else:
                d_lat_a, d_lon_a = meters_to_degrees(lat, offset, -limit)
                d_lat_b, d_lon_b = meters_to_degrees(lat, offset, limit)
            features.append(
                {
                    "type": "Feature",
                    "properties": {
                        "name": f"{place} corridor {index + 1}",
                        "highway": road,
                        "length": round(limit * 2, 1),
                    },
                    "geometry": {
                        "type": "LineString",
                        "coordinates": [
                            [round(lon + d_lon_a, 6), round(lat + d_lat_a, 6)],
                            [round(lon + d_lon_b, 6), round(lat + d_lat_b, 6)],
                        ],
                    },
                }
            )
            road_mix[road] += 1
            total_length_m += limit * 2

    area_sqkm = pi * (radius_m / 1000) ** 2
    d_lat, d_lon = meters_to_degrees(lat, radius_m, radius_m)
    mix_items = [
        {"type": key, "count": count}
        for key, count in sorted(road_mix.items(), key=lambda i: i[1], reverse=True)
        if count
    ]

    # Build a routable graph from the synthetic features so tools still work.
    graph = nx.Graph()
    node_coords: dict[int, tuple[float, float]] = {}
    for index, feature in enumerate(features):
        (lon_a, lat_a), (lon_b, lat_b) = feature["geometry"]["coordinates"]
        a_id, b_id = index * 2, index * 2 + 1
        node_coords[a_id] = (lat_a, lon_a)
        node_coords[b_id] = (lat_b, lon_b)
        graph.add_edge(a_id, b_id, length=haversine_m(lat_a, lon_a, lat_b, lon_b))

    return {
        "geojson": {"type": "FeatureCollection", "features": features},
        "center": [lat, lon],
        "bounds": [[lat - d_lat, lon - d_lon], [lat + d_lat, lon + d_lon]],
        "orientation": {"bins": [0.0] * ORIENTATION_BINS,
                        "bin_count": ORIENTATION_BINS, "order": 50, "entropy": 0.5},
        "_graph": graph,
        "_nodes": node_coords,
        "stats": {
            "place": place,
            "network_type": network_type,
            "radius_m": radius_m,
            "nodes": len(offsets) * len(offsets),
            "edges": len(features),
            "intersections": len(offsets) * len(offsets),
            "dead_ends": 0,
            "total_km": round(total_length_m / 1000, 2),
            "km_per_sqkm": round((total_length_m / 1000) / area_sqkm, 2),
            "intersection_density": round((len(offsets) ** 2) / area_sqkm, 1),
            "dead_end_ratio": 0.0,
            "circuity": 1.0,
            "avg_segment_m": round(total_length_m / max(len(features), 1), 1),
            "connectivity_index": 70,
            "grid_order": 50,
            "road_mix": mix_items,
            "source": "sample grid (Overpass unreachable)",
        },
    }


# --------------------------------------------------------------------------- #
# Orchestration
# --------------------------------------------------------------------------- #


def analyze(place: str, network_type: str, radius_m: int) -> dict[str, Any]:
    """Public entry: geocode, then delegate to the coord-keyed cache.

    Keying the heavy work on rounded coordinates means /api/network and the
    analytics endpoints share one cache entry even if the place strings differ
    (typed name vs. 'lat,lon' vs. resolved label).
    """
    lat, lon, label = geocode_place(place)
    base = _analyze_coords(round(lat, 5), round(lon, 5), network_type, radius_m)
    # Overlay the human label without mutating the shared cached object.
    out = dict(base)
    out["stats"] = dict(base["stats"])
    out["stats"]["place"] = label
    return out


@lru_cache(maxsize=64)
def _analyze_coords(lat: float, lon: float, network_type: str,
                    radius_m: int) -> dict[str, Any]:
    label = f"{lat:.4f}, {lon:.4f}"
    with ThreadPoolExecutor(max_workers=2) as pool:
        streets_future = pool.submit(fetch_streets, lat, lon, radius_m, network_type)
        pois_future = pool.submit(fetch_pois, lat, lon, radius_m)
        try:
            raw_streets = streets_future.result()
        except RuntimeError:
            # No silent synthetic-data swap in production. Offline dev can opt in.
            if os.environ.get("GIS_ALLOW_DEMO") == "1":
                result = build_demo_network(label, network_type, radius_m, lat, lon)
                result["pois"] = {"categories": {}, "total": 0, "shown": 0,
                                  "capped": False}
                result["insights"] = build_insights(result["stats"], result["pois"])
                result["access"] = None
                return result
            raise
        try:
            raw_pois = pois_future.result()
        except Exception:  # noqa: BLE001 - POIs are non-fatal; streets are core
            raw_pois = {"elements": []}

    result = build_street_network(
        raw_streets, label, lat, lon, radius_m, network_type,
        "OpenStreetMap (Overpass live)",
    )
    pois = build_pois(raw_pois)
    result["pois"] = pois
    result["insights"] = build_insights(result["stats"], pois)
    try:
        result["access"] = compute_access(
            result["_graph"], result["_nodes"], pois["categories"], result["center"]
        )
    except Exception:  # noqa: BLE001 - access analysis is best-effort
        result["access"] = None
    return result


def clamp_radius(raw: Any, network_type: str) -> int:
    radius_m = min(max(int(raw), MIN_RADIUS_METERS), MAX_RADIUS_METERS)
    if network_type == "all":
        radius_m = min(radius_m, ALL_MODE_MAX_RADIUS)
    return radius_m


def friendly_error(exc: Exception) -> str:
    message = str(exc)
    if "Overpass" in message or "busy" in message:
        return "The map data service is busy right now. Please try again in a moment."
    return message


# --------------------------------------------------------------------------- #
# Web layer
# --------------------------------------------------------------------------- #

gis = Blueprint("gis", __name__)


@gis.get("/")
def index() -> Response:
    config = {
        "network": url_for("gis.network"),
        "geocode": url_for("gis.geocode"),
        "route": url_for("gis.route"),
        "isochrone": url_for("gis.isochrone"),
        "centrality": url_for("gis.centrality"),
        "whatif": url_for("gis.whatif"),
        "ask": url_for("gis.ask"),
    }
    html = PAGE.replace("__GIS_CONFIG__", json.dumps(config))
    return Response(html, mimetype="text/html")


@gis.get("/healthz")
def healthz() -> Any:
    # Booleans only - never the secret value.
    return jsonify({
        "status": "ok",
        "ask_configured": bool(os.environ.get("ANTHROPIC_API_KEY")),
        "upstash_configured": UPSTASH_ENABLED,
    })


@gis.get("/api/geocode")
def geocode() -> Any:
    query = request.args.get("q", "").strip()
    if len(query) < 2:
        return jsonify([])
    try:
        response = _session.get(
            f"{NOMINATIM_URL}/search",
            params={
                "q": query,
                "format": "jsonv2",
                "limit": 6,
                "accept-language": "en",
            },
            timeout=HTTP_TIMEOUT,
        )
        response.raise_for_status()
        suggestions = [
            {
                "name": item.get("display_name", query),
                "lat": float(item["lat"]),
                "lon": float(item["lon"]),
            }
            for item in response.json()
        ]
        return jsonify(suggestions)
    except Exception:  # noqa: BLE001
        return jsonify([])


@gis.get("/api/network")
def network() -> Any:
    place = request.args.get("place", DEFAULT_PLACE).strip()
    lat_raw = request.args.get("lat")
    lon_raw = request.args.get("lon")
    if lat_raw and lon_raw:
        place = f"{lat_raw},{lon_raw}"

    network_type = request.args.get("network", "drive").strip().lower()
    radius_raw = request.args.get("radius", "1500")

    if not place:
        return jsonify({"error": "Enter a country, city, or place name."}), 400
    if network_type not in NETWORK_TYPES:
        return jsonify({"error": "Choose drive, walk, bike, or all."}), 400

    try:
        radius_m = clamp_radius(radius_raw, network_type)
    except (ValueError, TypeError):
        return jsonify({"error": "Radius must be a number."}), 400

    try:
        result = analyze(place, network_type, radius_m)
        public = {k: v for k, v in result.items() if not k.startswith("_")}
        return jsonify(public)
    except Exception as exc:  # noqa: BLE001
        return jsonify({"error": friendly_error(exc)}), 502


def _load_graph() -> tuple[nx.Graph, dict, str]:
    """Resolve the cached analysis for the request's place/network/radius."""
    place = request.args.get("place", DEFAULT_PLACE).strip()
    network_type = request.args.get("network", "drive").strip().lower()
    if network_type not in NETWORK_TYPES:
        network_type = "drive"
    try:
        radius_m = clamp_radius(request.args.get("radius", "1500"), network_type)
    except (ValueError, TypeError):
        radius_m = 1500
    result = analyze(place, network_type, radius_m)
    return result["_graph"], result["_nodes"], network_type


@gis.get("/api/route")
def route() -> Any:
    try:
        graph, nodes, network_type = _load_graph()
        origin = (float(request.args["from_lat"]), float(request.args["from_lon"]))
        dest = (float(request.args["to_lat"]), float(request.args["to_lon"]))
        speed = SPEED_MPS.get(network_type, SPEED_MPS["drive"])
        return jsonify(compute_route(graph, nodes, origin, dest, speed))
    except (KeyError, ValueError):
        return jsonify({"error": "Provide from_lat, from_lon, to_lat, to_lon."}), 400
    except Exception as exc:  # noqa: BLE001
        return jsonify({"error": friendly_error(exc)}), 502


@gis.get("/api/isochrone")
def isochrone() -> Any:
    try:
        graph, nodes, network_type = _load_graph()
        origin = (float(request.args["lat"]), float(request.args["lon"]))
        minutes = max(1.0, min(60.0, float(request.args.get("minutes", "10"))))
        speed = SPEED_MPS.get(network_type, SPEED_MPS["drive"])
        return jsonify(compute_isochrone(graph, nodes, origin, minutes, speed))
    except (KeyError, ValueError):
        return jsonify({"error": "Provide lat, lon, and minutes."}), 400
    except Exception as exc:  # noqa: BLE001
        return jsonify({"error": friendly_error(exc)}), 502


@gis.get("/api/centrality")
def centrality() -> Any:
    try:
        graph, nodes, _ = _load_graph()
        return jsonify(compute_centrality(graph, nodes))
    except Exception as exc:  # noqa: BLE001
        return jsonify({"error": friendly_error(exc)}), 502


@gis.post("/api/whatif")
def whatif() -> Any:
    body = request.get_json(silent=True) or {}
    place = (body.get("place") or DEFAULT_PLACE).strip()
    network_type = (body.get("network") or "drive").strip().lower()
    if network_type not in NETWORK_TYPES:
        network_type = "drive"
    try:
        radius_m = clamp_radius(body.get("radius", 1500), network_type)
    except (ValueError, TypeError):
        radius_m = 1500
    interventions = body.get("interventions")
    if not isinstance(interventions, list) or not interventions:
        return jsonify({"error": "Add at least one change first."}), 400
    try:
        base = analyze(place, network_type, radius_m)
        return jsonify(apply_whatif(base, interventions))
    except Exception as exc:  # noqa: BLE001
        return jsonify({"error": friendly_error(exc)}), 502


# Abuse controls for /api/ask. Upstash Redis (REST) gives a single counter and
# cache shared across all serverless instances; if it's unset or unreachable we
# fall back to per-instance memory so the endpoint never breaks.
_ask_rate: dict[str, list[float]] = {}
_ask_cache: "OrderedDict[tuple, str]" = OrderedDict()


def _upstash(command: list[Any]) -> Any:
    """Run one Redis command via the Upstash REST API; returns its result."""
    resp = _session.post(
        UPSTASH_URL,
        headers={"Authorization": f"Bearer {UPSTASH_TOKEN}"},
        json=command,
        timeout=5,
    )
    resp.raise_for_status()
    return resp.json().get("result")


def _upstash_pipeline(commands: list[list[Any]]) -> list[Any]:
    resp = _session.post(
        f"{UPSTASH_URL}/pipeline",
        headers={"Authorization": f"Bearer {UPSTASH_TOKEN}"},
        json=commands,
        timeout=5,
    )
    resp.raise_for_status()
    return [item.get("result") for item in resp.json()]


def client_ip() -> str:
    forwarded = request.headers.get("x-forwarded-for", "")
    if forwarded:
        return forwarded.split(",")[0].strip()
    return request.remote_addr or "unknown"


def _mem_rate_limited(ip: str) -> bool:
    now = time.time()
    record = _ask_rate.get(ip)
    if record is None or now - record[0] >= ASK_RATE_WINDOW:
        _ask_rate[ip] = [now, 1]
        if len(_ask_rate) > 5000:  # opportunistic prune of stale windows
            cutoff = now - ASK_RATE_WINDOW
            for stale in [k for k, v in _ask_rate.items() if v[0] < cutoff]:
                _ask_rate.pop(stale, None)
        return False
    if record[1] >= ASK_RATE_LIMIT:
        return True
    record[1] += 1
    return False


def ask_rate_limited(ip: str) -> bool:
    if UPSTASH_ENABLED:
        try:
            # Time-bucketed fixed window: the key rotates each window, so a plain
            # EXPIRE keeps it a true fixed window without needing EXPIRE ... NX.
            bucket = int(time.time() // ASK_RATE_WINDOW)
            key = f"gis:rl:{ip}:{bucket}"
            count = _upstash_pipeline(
                [["INCR", key], ["EXPIRE", key, str(ASK_RATE_WINDOW)]]
            )[0]
            return int(count) > ASK_RATE_LIMIT
        except Exception:  # noqa: BLE001 - degrade to per-instance limiting
            pass
    return _mem_rate_limited(ip)


def _cache_key_str(key: tuple) -> str:
    return "gis:ac:" + "|".join(str(part) for part in key)


def ask_cache_get(key: tuple) -> str | None:
    if UPSTASH_ENABLED:
        try:
            return _upstash(["GET", _cache_key_str(key)])  # None on miss
        except Exception:  # noqa: BLE001 - fall back to memory
            pass
    value = _ask_cache.get(key)
    if value is not None:
        _ask_cache.move_to_end(key)
    return value


def ask_cache_put(key: tuple, value: str) -> None:
    if UPSTASH_ENABLED:
        try:
            _upstash(["SET", _cache_key_str(key), value, "EX", str(ASK_CACHE_TTL)])
            return
        except Exception:  # noqa: BLE001 - fall back to memory
            pass
    _ask_cache[key] = value
    _ask_cache.move_to_end(key)
    while len(_ask_cache) > ASK_CACHE_MAX:
        _ask_cache.popitem(last=False)


@gis.post("/api/ask")
def ask() -> Any:
    body = request.get_json(silent=True) or {}
    question = (body.get("question") or "").strip()[:500]
    if not question:
        return jsonify({"error": "Ask a question first."}), 400

    if ask_rate_limited(client_ip()):
        resp = jsonify({"error": "Too many questions in a short time. "
                                 "Please wait a moment and try again."})
        resp.status_code = 429
        resp.headers["Retry-After"] = str(ASK_RATE_WINDOW)
        return resp

    api_key = os.environ.get("ANTHROPIC_API_KEY")
    if not api_key:
        return jsonify({
            "error": "Ask the City is not enabled yet. The site owner needs to set "
                     "ANTHROPIC_API_KEY on the server.",
            "configured": False,
        }), 503
    try:
        import anthropic
    except Exception:  # noqa: BLE001
        return jsonify({"error": "Ask the City is unavailable (missing dependency).",
                        "configured": False}), 503

    place = (body.get("place") or DEFAULT_PLACE).strip()
    network_type = (body.get("network") or "drive").strip().lower()
    if network_type not in NETWORK_TYPES:
        network_type = "drive"
    try:
        radius_m = clamp_radius(body.get("radius", 1500), network_type)
    except (ValueError, TypeError):
        radius_m = 1500

    # Canonical cache key. Resolve coords first so a repeat question is answered
    # without re-fetching data or calling the model.
    try:
        lat, lon, label = geocode_place(place)
    except Exception as exc:  # noqa: BLE001
        return jsonify({"error": friendly_error(exc)}), 502
    q_norm = " ".join(question.lower().split())
    cache_key = (round(lat, 4), round(lon, 4), network_type, radius_m, q_norm)
    cached = ask_cache_get(cache_key)
    if cached is not None:
        return jsonify({"answer": cached, "place": label, "cached": True})

    try:
        result = analyze(place, network_type, radius_m)
    except Exception as exc:  # noqa: BLE001
        return jsonify({"error": friendly_error(exc)}), 502

    facts = build_fact_sheet(result)
    user_content = (f"City facts (JSON):\n{json.dumps(facts)}\n\n"
                    f"Question: {question}")
    try:
        client = anthropic.Anthropic(api_key=api_key)
        # No thinking (off by default on Opus 4.8) keeps this fast for serverless.
        message = client.messages.create(
            model=ASK_MODEL,
            max_tokens=800,
            system=ASK_SYSTEM,
            messages=[{"role": "user", "content": user_content}],
        )
        answer = "".join(
            b.text for b in message.content if getattr(b, "type", None) == "text"
        ).strip()
        if answer:
            ask_cache_put(cache_key, answer)
        return jsonify({"answer": answer or "No answer was produced.",
                        "place": result["stats"]["place"], "cached": False})
    except Exception as exc:  # noqa: BLE001
        return jsonify({"error": f"Ask the City failed: {exc}"}), 502


# --------------------------------------------------------------------------- #
# Frontend (single page; __GIS_CONFIG__ is replaced at request time)
# --------------------------------------------------------------------------- #

PAGE = r"""<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>GeoPulse GIS — Walkability Score & 15-Minute City Map</title>
  <meta name="description" content="Free walkability score and 15-minute-city map for any city. From live OpenStreetMap data: what you can reach on foot (groceries, healthcare, schools, transit, parks), plus shortest-path routing, travel-time isochrones, and street-network metrics. Built by Shahzad Asghar.">
  <link rel="canonical" href="https://shahzadasghar.com/gis/">
  <meta name="robots" content="index, follow">
  <meta property="og:type" content="website">
  <meta property="og:url" content="https://shahzadasghar.com/gis/">
  <meta property="og:title" content="GeoPulse GIS — Walkability Score & 15-Minute City Map">
  <meta property="og:description" content="Type any city and see, from real OpenStreetMap data, what you can reach in a 15-minute walk, plus routing, travel-time reach, and street-network analysis.">
  <meta name="twitter:card" content="summary_large_image">
  <meta name="twitter:title" content="GeoPulse GIS — Walkability Score & 15-Minute City Map">
  <meta name="twitter:description" content="Walkability scores, 15-minute-neighbourhood analysis, routing, and live street-network metrics for any city, from OpenStreetMap.">
  <script type="application/ld+json">
  {"@context":"https://schema.org","@type":"WebApplication","name":"GeoPulse GIS","url":"https://shahzadasghar.com/gis/","description":"Free walkability-score and 15-minute-city map. Scores any city's walkability, maps what is reachable on foot, and computes shortest-path routing, travel-time isochrones, and street-network metrics from live OpenStreetMap data.","applicationCategory":"Geographic Information System","keywords":"walkability score, 15-minute city, walk score, OpenStreetMap, street network analysis, isochrones, points of interest, urban accessibility, pedestrian access","featureList":["15-minute walkability score","What you can reach on foot","Shortest-path routing","Travel-time isochrones (reach)","Street-network metrics","Points-of-interest layers","Natural-language Ask the City"],"operatingSystem":"Web","browserRequirements":"Requires JavaScript","isAccessibleForFree":true,"creator":{"@id":"https://shahzadasghar.com/#shahzad-asghar"}}
  </script>
  <link rel="stylesheet" href="https://unpkg.com/leaflet@1.9.4/dist/leaflet.css">
  <style>
    :root{
      --ink:#101828;--muted:#667085;--line:rgba(16,24,40,.14);
      --panel:rgba(255,255,255,.96);--accent:#0f766e;--accent-d:#0b5b54;
      --bg:#eef2f7;
    }
    *{box-sizing:border-box}
    html,body{height:100%;margin:0}
    body{overflow:hidden;color:var(--ink);background:var(--bg);
      font-family:system-ui,-apple-system,"Segoe UI",Arial,sans-serif}
    .shell{display:grid;grid-template-columns:390px minmax(0,1fr);height:100vh;min-height:640px}
    aside{z-index:10;display:flex;flex-direction:column;gap:14px;min-width:0;
      padding:18px;overflow-y:auto;background:var(--panel);
      border-right:1px solid var(--line);box-shadow:12px 0 30px rgba(16,24,40,.08)}
    .brand{display:flex;align-items:center;justify-content:space-between;gap:12px}
    h1{margin:0;font-size:23px;line-height:1.1}
    h2{margin:0 0 10px;font-size:15px}
    .badge{flex:0 0 auto;padding:6px 8px;color:#0f5132;background:#d1fadf;
      border:1px solid #a6f4c5;border-radius:6px;font-size:12px;font-weight:700}
    .subtitle{margin:0;color:var(--muted);font-size:13px;line-height:1.45}
    form,.card{padding:14px;background:#fff;border:1px solid var(--line);border-radius:8px}
    label{display:block;margin-bottom:7px;color:#344054;font-size:12px;font-weight:700}
    input,select,button{width:100%;min-height:44px;border-radius:7px;font:inherit}
    input,select{padding:0 11px;color:var(--ink);background:#fff;
      border:1px solid #cfd6e4;outline:none;font-size:16px}
    input:focus,select:focus{border-color:var(--accent);
      box-shadow:0 0 0 3px rgba(15,118,110,.14)}
    .field{position:relative}
    .suggest{position:absolute;z-index:30;left:0;right:0;top:calc(100% + 4px);
      background:#fff;border:1px solid var(--line);border-radius:8px;
      box-shadow:0 12px 30px rgba(16,24,40,.16);max-height:240px;overflow:auto;display:none}
    .suggest.open{display:block}
    .suggest button{width:100%;min-height:0;padding:9px 11px;text-align:left;
      background:#fff;border:0;border-bottom:1px solid #f1f3f7;color:#344054;
      font-size:13px;cursor:pointer}
    .suggest button:hover,.suggest button.active{background:#f4f7fb}
    .grid{display:grid;grid-template-columns:1fr 1fr;gap:10px;margin-top:12px}
    .row{display:grid;grid-template-columns:1fr auto;gap:8px;margin-top:12px}
    button.primary{color:#fff;background:var(--accent);border:0;cursor:pointer;font-weight:700}
    button.primary:hover{background:var(--accent-d)}
    button.ghost{width:auto;min-height:44px;padding:0 13px;color:#344054;background:#f8fafc;
      border:1px solid #d9e2ef;cursor:pointer;font-weight:700}
    button:disabled{cursor:progress;opacity:.62}
    .chips{display:flex;flex-wrap:wrap;gap:8px;margin-top:12px}
    .chip{width:auto;min-height:32px;margin:0;padding:0 10px;color:#344054;
      background:#f8fafc;border:1px solid #d9e2ef;border-radius:7px;font-size:12px;
      font-weight:700;cursor:pointer}
    .chip:hover{border-color:var(--accent);color:var(--accent)}
    .stats{display:grid;grid-template-columns:1fr 1fr;gap:10px}
    .metric{min-height:70px;padding:10px;background:#f8fafc;border:1px solid #e4eaf3;border-radius:7px}
    .metric span{display:block;color:var(--muted);font-size:12px}
    .metric strong{display:block;margin-top:6px;font-size:19px;line-height:1}
    .bar{display:grid;grid-template-columns:84px minmax(0,1fr) 40px;align-items:center;
      gap:8px;margin:8px 0;font-size:12px}
    .track{height:8px;overflow:hidden;background:#e8edf5;border-radius:999px}
    .fill{display:block;height:100%;border-radius:999px}
    .toggle{display:flex;align-items:center;gap:9px;padding:8px 9px;margin-top:7px;
      background:#f8fafc;border:1px solid #e4eaf3;border-radius:7px;font-size:13px;cursor:pointer}
    .toggle input{width:18px;height:18px;min-height:0;margin:0}
    .toggle .dot{width:11px;height:11px;border-radius:50%;flex:0 0 auto}
    .toggle .n{margin-left:auto;color:var(--muted);font-weight:700}
    .decision{padding:9px 10px;margin-top:8px;background:#f8fafc;border:1px solid #e4eaf3;
      border-left:4px solid var(--accent);border-radius:7px;font-size:12px;line-height:1.4}
    .decision strong{display:block;margin-bottom:3px;font-size:13px}
    .access-head{display:flex;align-items:center;gap:14px}
    .score-ring{position:relative;width:74px;height:74px;border-radius:50%;flex:0 0 auto;
      background:conic-gradient(var(--ring,#cbd5e1) calc(var(--p,0)*3.6deg), #e8edf5 0)}
    .score-ring .inner{position:absolute;inset:6px;border-radius:50%;background:#fff;
      display:grid;place-items:center;line-height:1}
    .score-ring b{font-size:22px;color:var(--ink)}
    .score-ring i{font-style:normal;font-size:10px;color:var(--muted)}
    .access-grid{display:grid;grid-template-columns:1fr 1fr;gap:8px;margin-top:14px}
    .acc{display:flex;align-items:flex-start;gap:8px;padding:8px 9px;background:#f8fafc;
      border:1px solid #e4eaf3;border-radius:7px}
    .acc .dot{margin-top:3px;width:10px;height:10px;border-radius:50%;flex:0 0 auto}
    .acc .lbl{font-size:12px;font-weight:700;line-height:1.2}
    .acc .meta{margin-top:2px;font-size:11px;color:var(--muted)}
    details.details{padding:0}
    details.details>summary{padding:14px;cursor:pointer;font-size:14px;font-weight:700;
      color:#344054;list-style:none}
    details.details>summary::-webkit-details-marker{display:none}
    details.details>summary::after{content:"  +";color:var(--muted)}
    details.details[open]>summary::after{content:"  -"}
    details.details>*:not(summary){margin-left:14px;margin-right:14px}
    details.details>*:last-child{margin-bottom:14px}
    .sub-h{margin:16px 0 8px;font-size:13px;color:#344054}
    .foot{padding:14px;color:var(--muted);font-size:11px;line-height:1.5;
      border-top:1px solid var(--line)}
    .foot strong{display:block;color:#344054;font-size:12px;margin-bottom:4px}
    .foot span{display:block;margin-top:4px}
    .foot a{color:var(--accent)}
    details.method{margin-top:10px}
    details.method>summary{cursor:pointer;font-size:12px;font-weight:700;color:var(--accent);list-style:none}
    details.method>summary::-webkit-details-marker{display:none}
    details.method>summary::after{content:" +"}
    details.method[open]>summary::after{content:" -"}
    details.whatif{padding:0}
    details.whatif>summary{display:flex;align-items:center;gap:8px;padding:14px;cursor:pointer;
      font-size:15px;font-weight:700;color:#101828;list-style:none}
    details.whatif>summary::-webkit-details-marker{display:none}
    details.whatif>summary::before{content:"";width:9px;height:9px;border-radius:50%;background:#7c3aed;flex:0 0 auto}
    details.whatif>summary::after{content:"+";margin-left:auto;color:var(--muted);font-weight:700}
    details.whatif[open]>summary::after{content:"\2013"}
    details.whatif>*:not(summary){margin-left:14px;margin-right:14px}
    details.whatif>*:last-child{margin-bottom:14px}
    .ask h2{display:flex;align-items:center;gap:8px}
    .ask h2::before{content:"";width:9px;height:9px;border-radius:50%;background:#2563eb}
    .ask-answer{margin-top:11px;font-size:13px;line-height:1.55;color:#344054}
    .ask-answer:empty{display:none}
    .ask-answer.loading{color:var(--muted)}
    .ask-answer p{margin:0 0 8px}
    .ask-answer p:last-child{margin-bottom:0}
    .ask-answer p.h{font-weight:700;color:#101828;margin:10px 0 4px}
    .ask-answer ul{margin:6px 0;padding-left:18px}
    .ask-answer li{margin:3px 0}
    .ask-answer strong{color:#101828}
    button.armed{background:var(--accent)!important;color:#fff!important;border-color:var(--accent)!important}
    .wi-delta{margin-top:12px;padding:11px;border-radius:8px;border:1px solid #e4eaf3;background:#f8fafc}
    .wi-delta .big{font-size:16px;font-weight:800;line-height:1.3}
    .wi-delta .up{color:#12b76a}.wi-delta .down{color:#f04438}.wi-delta .flat{color:var(--muted)}
    .wi-row{display:flex;justify-content:space-between;gap:8px;font-size:12px;margin-top:5px}
    main{position:relative;min-width:0;height:100vh}
    #map{position:absolute;inset:0;background:#e8eef6}
    /* top-right info card (legend lives in its own panel now) */
    .map-card{position:absolute;z-index:500;right:14px;top:14px;width:min(320px,calc(100% - 28px));
      padding:11px 13px;background:var(--panel);border:1px solid var(--line);border-radius:10px;
      box-shadow:0 10px 28px rgba(16,24,40,.16)}
    .map-card strong{display:block;font-size:15px}
    .map-card span{display:block;margin-top:3px;color:var(--muted);font-size:12.5px;line-height:1.35}
    .status{position:absolute;z-index:700;left:50%;bottom:18px;max-width:min(620px,calc(100% - 48px));
      padding:10px 12px;color:#344054;background:#fff;border:1px solid var(--line);border-radius:8px;
      box-shadow:0 10px 25px rgba(16,24,40,.12);transform:translateX(-50%);font-size:13px}
    .status.error{color:#7a271a;background:#fff4ed;border-color:#f9dbaf}
    .status.busy::after{content:"";display:inline-block;width:12px;height:12px;margin-left:8px;
      vertical-align:-2px;border:2px solid #cfd6e4;border-top-color:var(--accent);
      border-radius:50%;animation:spin .8s linear infinite}
    @keyframes spin{to{transform:rotate(360deg)}}
    /* top-left grouped toolbar (single container, never under another panel) */
    .tools{position:absolute;z-index:600;left:14px;top:14px;display:flex;flex-direction:column;gap:6px;
      padding:7px;background:var(--panel);border:1px solid var(--line);border-radius:12px;
      box-shadow:0 10px 28px rgba(16,24,40,.16);max-width:calc(100% - 28px)}
    .tools-row{display:flex;flex-wrap:wrap;align-items:center;gap:6px}
    .tools .tool{width:auto;min-height:40px;padding:0 13px;background:#fff;color:#344054;
      border:1px solid var(--line);border-radius:8px;font-size:13px;font-weight:700;cursor:pointer;transition:.12s}
    .tools .tool:hover{border-color:var(--accent);color:var(--accent)}
    .tools .tool.on{background:var(--accent);color:#fff;border-color:var(--accent);
      box-shadow:0 0 0 3px rgba(15,118,110,.2)}
    .tools .tool.danger:hover{border-color:#f04438;color:#f04438}
    .tools .tool:focus-visible{outline:3px solid rgba(15,118,110,.45);outline-offset:1px}
    .reach-group{display:inline-flex;align-items:stretch;border:1px solid var(--line);
      border-radius:8px;overflow:hidden}
    .reach-group .tool{border:0;border-radius:0;min-height:40px}
    .reach-group .tool.on{box-shadow:none}
    .reach-group select{width:auto;min-height:40px;padding:0 6px;border:0;border-left:1px solid var(--line);
      background:#f1f5f9;color:#344054;font-size:12px;font-weight:700;outline:none}
    .tools-sep{width:1px;align-self:stretch;background:var(--line);margin:3px 1px}
    .tools-hint{font-size:11.5px;color:var(--muted);padding:0 4px 1px}
    .tools-hint.active{color:var(--accent);font-weight:700}
    /* bottom-left collapsible legend */
    .legend-panel{position:absolute;z-index:550;left:14px;bottom:18px;padding:8px 11px;
      background:var(--panel);border:1px solid var(--line);border-radius:10px;
      box-shadow:0 10px 28px rgba(16,24,40,.16);max-width:min(330px,calc(100% - 28px))}
    .legend-toggle{display:flex;align-items:center;justify-content:space-between;gap:10px;width:100%;
      background:none;border:0;cursor:pointer;font-size:12px;font-weight:800;color:#344054;padding:0;min-height:0}
    .legend-toggle .caret{transition:transform .15s}
    .legend-toggle[aria-expanded="false"] .caret{transform:rotate(-90deg)}
    .legend{display:grid;grid-template-columns:1fr 1fr;gap:4px 16px;margin-top:8px;font-size:12px;color:#475467}
    .legend.hidden{display:none}
    .legend span{display:flex;align-items:center;gap:7px;white-space:nowrap}
    .legend i{display:inline-block;width:12px;height:12px;border-radius:3px;flex:0 0 auto}
    .legend b{margin-left:auto;color:#101828;font-weight:700}
    @media (max-width:900px){
      body{overflow:auto}
      .shell{display:block;height:auto}
      aside{height:auto;border-right:0;border-bottom:1px solid var(--line)}
      main{height:66vh;min-height:440px}
      .map-card{left:10px;right:10px;top:10px;width:auto}
      .tools{left:10px;right:10px;top:auto;bottom:10px;max-width:none}
      .tools-row{flex-wrap:nowrap;overflow-x:auto;justify-content:flex-start;-webkit-overflow-scrolling:touch}
      .tools .tool{flex:0 0 auto}
      .status{bottom:76px}
      .legend-panel{display:none}
    }
  </style>
</head>
<body>
  <div class="shell">
    <aside>
      <div>
        <div class="brand">
          <h1>GeoPulse GIS</h1>
          <span class="badge">Live OSM</span>
        </div>
        <p class="subtitle">Search any city or place and analyse its real street
          network and points of interest from OpenStreetMap.</p>
      </div>

      <form id="searchForm" autocomplete="off">
        <label for="place">Country, city, place, or "lat, lon"</label>
        <div class="field">
          <input id="place" name="place" value="San Francisco, California"
            aria-label="Search location" aria-autocomplete="list">
          <div id="suggest" class="suggest" role="listbox" aria-label="Suggestions"></div>
        </div>
        <div class="grid">
          <div>
            <label for="network">Travel mode</label>
            <select id="network" name="network">
              <option value="drive">Drive</option>
              <option value="walk">Walk</option>
              <option value="bike">Bike</option>
              <option value="all">All paths</option>
            </select>
          </div>
          <div>
            <label for="radius">Radius</label>
            <select id="radius" name="radius">
              <option value="1000">1 km</option>
              <option value="1500" selected>1.5 km</option>
              <option value="3000">3 km</option>
              <option value="5000">5 km</option>
              <option value="8000">8 km</option>
              <option value="10000">10 km</option>
            </select>
          </div>
        </div>
        <div class="row">
          <button id="runButton" type="submit" class="primary">Analyze location</button>
          <button id="locateButton" type="button" class="ghost" title="Use my location">My location</button>
        </div>
        <div class="chips" id="chips">
          <button class="chip" type="button" data-place="London, United Kingdom">London</button>
          <button class="chip" type="button" data-place="Tokyo, Japan">Tokyo</button>
          <button class="chip" type="button" data-place="Paris, France">Paris</button>
          <button class="chip" type="button" data-place="New York, New York">New York</button>
          <button class="chip" type="button" data-place="Amman, Jordan">Amman</button>
        </div>
      </form>

      <section class="card access" aria-label="Everyday access">
        <div class="access-head">
          <div class="score-ring" id="scoreRing"><div class="inner"><b id="accessScore">--</b><i>/100</i></div></div>
          <div>
            <h2 style="margin:0 0 4px">15-minute neighbourhood</h2>
            <p class="subtitle" id="accessVerdict">See what you can reach on foot from here.</p>
          </div>
        </div>
        <div class="access-grid" id="accessGrid"></div>
        <p class="subtitle" id="accessSummary" style="margin-top:10px"></p>
        <details class="method">
          <summary>How this score is calculated</summary>
          <p class="subtitle" id="accessMethod"></p>
        </details>
      </section>

      <section class="card ask" id="askCard">
        <h2>Ask the City</h2>
        <p class="subtitle">Ask a question in plain English. Answers are grounded in this location's real data.</p>
        <div class="field">
          <input id="askInput" placeholder="e.g. Is this a good area to live without a car?"
            aria-label="Ask a question about this place">
        </div>
        <div class="chips" id="askChips">
          <button class="chip" type="button" data-q="Is this a good area to live without a car, and why?">Car-free living?</button>
          <button class="chip" type="button" data-q="What everyday services are missing within a short walk here?">What's missing?</button>
          <button class="chip" type="button" data-q="How walkable is this area and what stands out about its streets?">How walkable?</button>
        </div>
        <button class="primary" type="button" id="askBtn" style="margin-top:10px">Ask</button>
        <div id="askAnswer" class="ask-answer"></div>
      </section>

      <details class="card whatif" id="whatifCard">
        <summary>What-If Studio</summary>
        <p class="subtitle">Propose a change and see the walkability impact, recomputed on the live street graph.</p>
        <div class="grid">
          <select id="wiCategory" aria-label="Amenity type">
            <option value="food_retail">Food &amp; retail</option>
            <option value="healthcare">Healthcare</option>
            <option value="education">Education</option>
            <option value="transit">Transit &amp; fuel</option>
            <option value="civic">Civic &amp; finance</option>
            <option value="leisure">Parks &amp; leisure</option>
          </select>
          <button class="ghost" type="button" id="wiAddBtn">Add a place</button>
        </div>
        <button class="ghost" type="button" id="wiCloseBtn" style="margin-top:8px">Close a street / area</button>
        <p class="subtitle" id="wiHint" style="margin-top:8px">Pick a mode, then click the map to drop changes.</p>
        <div class="grid" style="margin-top:8px">
          <button class="primary" type="button" id="wiRun" disabled>Recompute</button>
          <button class="ghost" type="button" id="wiReset" disabled>Reset</button>
        </div>
        <div id="wiResult"></div>
      </details>

      <section class="card">
        <h2>What is nearby</h2>
        <div id="poiToggles"></div>
      </section>

      <details class="card details">
        <summary>Network details (for analysts)</summary>
        <section class="stats" aria-label="Network statistics" style="margin-top:12px">
          <div class="metric"><span>Street segments</span><strong id="m-edges">-</strong></div>
          <div class="metric"><span>Intersections</span><strong id="m-int">-</strong></div>
          <div class="metric"><span>Total length</span><strong id="m-len">-</strong></div>
          <div class="metric"><span>Density</span><strong id="m-den">-</strong></div>
          <div class="metric"><span>Connectivity index</span><strong id="m-conn">-</strong></div>
          <div class="metric"><span>Points of interest</span><strong id="m-poi">-</strong></div>
        </section>
        <h3 class="sub-h">Road mix</h3>
        <div id="roadMix"></div>
        <h3 class="sub-h">Street orientation</h3>
        <canvas id="rose" width="320" height="320"
          style="display:block;margin:0 auto;width:100%;max-width:240px"></canvas>
        <p class="subtitle" id="roseNote" style="text-align:center;margin-top:6px"></p>
        <h3 class="sub-h">Computed insights</h3>
        <p class="subtitle" id="insightLead">Run an analysis to compute network structure.</p>
        <div id="decisions"></div>
      </details>

      <section class="card">
        <h2>Export</h2>
        <div class="grid">
          <button class="ghost" type="button" id="exportGeo">GeoJSON</button>
          <button class="ghost" type="button" id="exportPng">PNG image</button>
        </div>
      </section>

      <footer class="foot">
        <strong>GeoPulse GIS</strong>
        <span>Live analysis built from OpenStreetMap. Data &copy; OpenStreetMap
          contributors, under the Open Database License (ODbL).</span>
        <span>Walkability is estimated from mapped streets and points of interest,
          not a survey. Part of <a href="/">shahzadasghar.com</a>.</span>
      </footer>
    </aside>

    <main>
      <div id="map"></div>

      <div class="tools" role="toolbar" aria-label="Map tools">
        <div class="tools-row">
          <button type="button" id="routeBtn" class="tool" aria-pressed="false" aria-label="Route: shortest path between two points">Route</button>
          <span class="reach-group">
            <button type="button" id="isoBtn" class="tool" aria-pressed="false" aria-label="Reach: travel reach from a point">Reach</button>
            <select id="isoMin" aria-label="Reach time in minutes">
              <option value="5">5 min</option>
              <option value="10" selected>10 min</option>
              <option value="15">15 min</option>
              <option value="20">20 min</option>
              <option value="30">30 min</option>
            </select>
          </span>
          <button type="button" id="centralityBtn" class="tool" aria-pressed="false" aria-label="Corridors: highest-traffic streets">Corridors</button>
          <button type="button" id="measureBtn" class="tool" aria-pressed="false" aria-label="Measure distance and area">Measure</button>
          <span class="tools-sep" aria-hidden="true"></span>
          <button type="button" id="clearToolsBtn" class="tool danger" aria-label="Clear all overlays">Clear</button>
        </div>
        <div class="tools-hint" id="toolsHint">Pick a tool, then click the map.</div>
      </div>

      <div class="map-card">
        <strong id="mapTitle">Ready for analysis</strong>
        <span id="mapSubtitle">A fresh street graph is built from OpenStreetMap for the selected location.</span>
      </div>

      <div class="legend-panel" id="legendPanel">
        <button class="legend-toggle" id="legendToggle" aria-expanded="true" aria-controls="legend">
          <span>Legend</span><span class="caret" aria-hidden="true">&#9662;</span>
        </button>
        <div class="legend" id="legend"></div>
      </div>

      <div id="status" class="status" role="status" aria-live="polite">Loading San Francisco as the opening example&hellip;</div>
    </main>
  </div>

  <script src="https://unpkg.com/leaflet@1.9.4/dist/leaflet.js"></script>
  <script src="https://unpkg.com/leaflet-image@0.4.0/leaflet-image.js"></script>
  <script>
    const CONFIG = __GIS_CONFIG__;
    const $ = (id) => document.getElementById(id);

    const ROAD_COLORS = {motorway:"#dc2626",trunk:"#ea580c",primary:"#d97706",
      secondary:"#2563eb",tertiary:"#0f766e",residential:"#475467",service:"#98a2b3",
      living_street:"#7c3aed",footway:"#7c3aed",cycleway:"#0891b2",path:"#7c3aed",
      track:"#a16207",pedestrian:"#9333ea",steps:"#9333ea",unclassified:"#667085",road:"#667085"};
    // Colour-blind-safe (Paul Tol). Distinct hues; Roads is grey, never an amber.
    const POI_COLORS = {healthcare:"#CC3311",education:"#EE3377",food_retail:"#EE7733",
      transit:"#0077BB",civic:"#009988",leisure:"#228833"};
    const ROAD_LEGEND_COLOR = "#555555";

    const map = L.map("map",{preferCanvas:true,zoomControl:true}).setView([37.7749,-122.4194],13);
    const light = L.tileLayer("https://{s}.basemaps.cartocdn.com/light_all/{z}/{x}/{y}{r}.png",
      {maxZoom:20,crossOrigin:true,attribution:"&copy; OpenStreetMap contributors &copy; CARTO"}).addTo(map);
    const dark = L.tileLayer("https://{s}.basemaps.cartocdn.com/dark_all/{z}/{x}/{y}{r}.png",
      {maxZoom:20,crossOrigin:true,attribution:"&copy; OpenStreetMap contributors &copy; CARTO"});
    const osm = L.tileLayer("https://tile.openstreetmap.org/{z}/{x}/{y}.png",
      {maxZoom:19,crossOrigin:true,attribution:"&copy; OpenStreetMap contributors"});
    L.control.layers({"Light":light,"Dark":dark,"OpenStreetMap":osm},{},{collapsed:true}).addTo(map);

    let streetLayer=null, haloLayer=null, lastData=null, walkZoneLayer=null;
    let poiLayers={};
    let wiMode=null, wiInterventions=[], wiMarkers=[], wiZoneLayer=null, wiClosedLayer=null;

    function roadType(f){const v=f.properties.highway||"unclassified";return Array.isArray(v)?v[0]:v;}
    function styleRoad(f){const t=roadType(f);const major=["motorway","trunk","primary"].includes(t);
      return {color:ROAD_COLORS[t]||ROAD_COLORS.unclassified,weight:major?3.6:2,opacity:.85,lineCap:"round"};}
    function styleHalo(f){const major=["motorway","trunk","primary"].includes(roadType(f));
      return {color:"#fff",weight:major?7:4.2,opacity:.7,lineCap:"round"};}
    function nFmt(v){return new Intl.NumberFormat().format(Math.round(v));}
    function kmFmt(v){return Number(v).toLocaleString(undefined,{maximumFractionDigits:1})+" km";}

    function setStatus(msg,kind){const s=$("status");s.textContent=msg;
      s.classList.toggle("error",kind==="error");s.classList.toggle("busy",kind==="busy");}
    function setLoading(on){$("runButton").disabled=on;$("runButton").textContent=on?"Analyzing...":"Analyze location";}

    function popupRoad(f){const p=f.properties;const len=Number(p.length||0);
      const s=len>=1000?(len/1000).toFixed(2)+" km":Math.round(len)+" m";
      return `<strong>${p.name||"Unnamed street"}</strong><br>Type: ${roadType(f)}<br>Length: ${s}`;}

    function renderNetwork(data){
      [streetLayer,haloLayer].forEach(l=>{if(l)map.removeLayer(l);});
      Object.values(poiLayers).forEach(l=>map.removeLayer(l));
      poiLayers={};

      haloLayer=L.geoJSON(data.geojson,{style:styleHalo}).addTo(map);
      streetLayer=L.geoJSON(data.geojson,{style:styleRoad,onEachFeature:(f,layer)=>{
        layer.bindPopup(popupRoad(f));
        layer.on({mouseover:e=>{e.target.setStyle({color:"#101828",weight:5,opacity:1});e.target.bringToFront();},
          mouseout:e=>streetLayer.resetStyle(e.target)});
      }}).addTo(map);

      const cats=data.pois?data.pois.categories:{};
      Object.entries(cats).forEach(([key,info])=>{
        if(!info.count)return;
        const color=POI_COLORS[key]||"#2563eb";
        poiLayers[key]=L.geoJSON(info.geojson,{pointToLayer:(f,ll)=>L.circleMarker(ll,
          {radius:6,color:"#fff",weight:1.5,fillColor:color,fillOpacity:.85}),
          onEachFeature:(f,layer)=>layer.bindPopup(
            `<strong>${f.properties.name}</strong><br>${info.label} &middot; ${f.properties.kind}`)
        }).addTo(map);
      });

      if(walkZoneLayer){map.removeLayer(walkZoneLayer);walkZoneLayer=null;}
      const zone=data.access&&data.access.zone;
      if(zone){
        walkZoneLayer=L.geoJSON(zone,{style:{color:"#0f766e",weight:2,dashArray:"6 5",
          fillColor:"#0f766e",fillOpacity:.08}}).addTo(map);
        walkZoneLayer.bringToBack();
        walkZoneLayer.bindTooltip(`Approx. ${zone.properties.minutes}-minute walk`,{sticky:true});
      }

      try{map.fitBounds(data.bounds,{padding:[28,28]});}catch(e){}
    }

    function renderAccess(a){
      const ring=$("scoreRing");
      if(!a){ring.style.setProperty("--p",0);$("accessScore").textContent="--";
        $("accessVerdict").textContent="No walk analysis available for this area.";
        $("accessGrid").innerHTML="";$("accessSummary").textContent="";
        if($("accessMethod"))$("accessMethod").textContent="";return;}
      if($("accessMethod")&&a.method){
        const f=a.factors||{};
        $("accessMethod").textContent=`${a.method} For this area — coverage ${Math.round((f.coverage||0)*100)}%, abundance ${Math.round((f.abundance||0)*100)}%, proximity ${Math.round((f.proximity||0)*100)}%. Capped at 99. Data: OpenStreetMap.`;
      }
      ring.style.setProperty("--p",a.score);
      const col=a.score>=80?"#12b76a":a.score>=60?"#84cc16":a.score>=40?"#f79009":"#f04438";
      ring.style.setProperty("--ring",col);
      $("accessScore").textContent=a.score;
      $("accessVerdict").textContent=a.verdict;
      $("accessSummary").textContent=a.summary;
      $("accessGrid").innerHTML=a.categories.map(c=>
        `<div class="acc"><span class="dot" style="background:${POI_COLORS[c.key]||'#2563eb'};opacity:${c.present?1:.3}"></span>
          <div><div class="lbl">${c.label}</div><div class="meta">${c.present
            ?`${c.count} nearby &middot; nearest ${c.nearest_min} min`
            :`none within ${a.minutes} min`}</div></div></div>`).join("");
    }

    function renderStats(s){
      $("m-edges").textContent=nFmt(s.edges);
      $("m-int").textContent=nFmt(s.intersections);
      $("m-len").textContent=kmFmt(s.total_km);
      $("m-den").textContent=s.km_per_sqkm.toFixed(1)+" km/km2";
      $("m-conn").textContent=s.connectivity_index+"/100";
      const poi=lastData.pois?lastData.pois.total:0;
      $("m-poi").textContent=nFmt(poi);

      const max=Math.max(...s.road_mix.map(i=>i.count),1);
      $("roadMix").innerHTML=s.road_mix.slice(0,7).map(i=>
        `<div class="bar"><span>${i.type}</span><span class="track"><span class="fill"
         style="width:${(i.count/max)*100}%;background:${ROAD_COLORS[i.type]||ROAD_COLORS.unclassified}"></span></span>
         <strong>${i.count}</strong></div>`).join("");

      $("mapTitle").textContent=s.place;
      $("mapSubtitle").textContent=`${s.network_type.toUpperCase()} network | ${nFmt(s.edges)} segments | ${kmFmt(s.total_km)} | ${s.source}`;
      const cats=lastData.pois?lastData.pois.categories:{};
      $("legend").innerHTML=
        `<span><i style="background:${ROAD_LEGEND_COLOR}"></i>Roads</span>`+
        Object.entries(POI_COLORS).map(([k,c])=>{const info=cats[k]||{};
          const cnt=info.count?`<b>${nFmt(info.count)}</b>`:"";
          return `<span><i style="background:${c}"></i>${info.label||k}${cnt}</span>`;}).join("");
    }

    function renderPois(pois){
      const wrap=$("poiToggles");
      const entries=Object.entries(pois.categories).filter(([,v])=>v.count>0);
      if(!entries.length){wrap.innerHTML='<p class="subtitle">No points of interest returned.</p>';return;}
      wrap.innerHTML="";
      entries.forEach(([key,info])=>{
        const id="poi-"+key;
        const el=document.createElement("label");
        el.className="toggle";el.setAttribute("for",id);
        el.innerHTML=`<input type="checkbox" id="${id}" checked>
          <span class="dot" style="background:${POI_COLORS[key]||"#2563eb"}"></span>
          <span>${info.label}</span><span class="n">${info.count}</span>`;
        wrap.appendChild(el);
        el.querySelector("input").addEventListener("change",(e)=>{
          const layer=poiLayers[key];if(!layer)return;
          if(e.target.checked)layer.addTo(map);else map.removeLayer(layer);
        });
      });
      if(pois.capped){
        const note=document.createElement("p");note.className="subtitle";
        note.style.marginTop="8px";
        note.textContent=`Showing ${nFmt(pois.shown)} of ${nFmt(pois.total)} points (capped for performance).`;
        wrap.appendChild(note);
      }
    }

    function renderInsights(list){
      $("insightLead").textContent=list.length?list[0].detail:"No analysis available.";
      $("decisions").innerHTML=list.map(i=>
        `<div class="decision"><strong>${i.title}</strong>${i.detail}</div>`).join("");
    }

    let lastQuery=null;
    async function analyze(coords){
      const place=coords?`${coords.lat.toFixed(6)}, ${coords.lon.toFixed(6)}`:$("place").value.trim();
      lastQuery={place,network:$("network").value,radius:$("radius").value};
      const params=new URLSearchParams(lastQuery);
      setLoading(true);setStatus(`Building street graph for ${place}...`,"busy");
      try{
        const res=await fetch(`${CONFIG.network}?${params.toString()}`);
        const data=await res.json();
        if(!res.ok)throw new Error(data.error||"Analysis failed.");
        lastData=data;
        if(typeof clearTools==="function")clearTools();
        renderNetwork(data);renderStats(data.stats);
        renderPois(data.pois||{categories:{}});renderInsights(data.insights||[]);
        renderRose(data.orientation||{});renderAccess(data.access);
        const warn=data.stats.source.includes("unreachable");
        setStatus(`${warn?"Sample data shown - ":""}Analysis ready: ${data.stats.place}`,warn?"error":"");
      }catch(err){setStatus(err.message,"error");}
      finally{setLoading(false);}
    }

    function baseParams(extra){
      const base=lastQuery||{place:$("place").value.trim(),network:$("network").value,radius:$("radius").value};
      return new URLSearchParams(Object.assign({},base,extra||{})).toString();
    }

    function renderRose(o){
      const cv=$("rose");if(!cv)return;const ctx=cv.getContext("2d");
      const W=cv.width,H=cv.height,cx=W/2,cy=H/2,R=Math.min(W,H)/2-30;
      ctx.clearRect(0,0,W,H);
      const bins=o.bins||[];const n=bins.length||0;
      ctx.strokeStyle="#e4eaf3";ctx.lineWidth=1;
      [0.5,1].forEach(f=>{ctx.beginPath();ctx.arc(cx,cy,R*f,0,2*Math.PI);ctx.stroke();});
      ctx.fillStyle="#98a2b3";ctx.font="11px system-ui";ctx.textAlign="center";ctx.textBaseline="middle";
      ctx.fillText("N",cx,cy-R-12);ctx.fillText("S",cx,cy+R+12);
      ctx.fillText("E",cx+R+12,cy);ctx.fillText("W",cx-R-12,cy);
      if(!n){$("roseNote").textContent="";return;}
      const max=Math.max(...bins,1e-6),half=(360/n)/2*Math.PI/180,step=360/n;
      ctx.fillStyle="rgba(15,118,110,.78)";
      for(let i=0;i<n;i++){
        const r=R*(bins[i]/max);if(r<=0)continue;
        const b=i*step*Math.PI/180;
        ctx.beginPath();ctx.moveTo(cx,cy);
        ctx.lineTo(cx+r*Math.sin(b-half),cy-r*Math.cos(b-half));
        ctx.lineTo(cx+r*Math.sin(b+half),cy-r*Math.cos(b+half));
        ctx.closePath();ctx.fill();
      }
      $("roseNote").textContent=`Grid-order ${o.order}/100 (length-weighted bearings).`;
    }

    /* ----- autocomplete ----- */
    let suggestTimer=null, suggestItems=[], suggestIndex=-1;
    const suggestBox=$("suggest");
    function closeSuggest(){suggestBox.classList.remove("open");suggestBox.innerHTML="";suggestIndex=-1;}
    function renderSuggest(items){
      suggestItems=items;
      if(!items.length){closeSuggest();return;}
      suggestBox.innerHTML=items.map((it,i)=>
        `<button type="button" role="option" data-i="${i}">${it.name}</button>`).join("");
      suggestBox.classList.add("open");
      suggestBox.querySelectorAll("button").forEach(b=>b.addEventListener("click",()=>{
        const it=items[b.dataset.i];
        $("place").value=it.name;closeSuggest();
        analyze({lat:it.lat,lon:it.lon});
      }));
    }
    $("place").addEventListener("input",()=>{
      const q=$("place").value.trim();
      clearTimeout(suggestTimer);
      if(q.length<3){closeSuggest();return;}
      suggestTimer=setTimeout(async()=>{
        try{const r=await fetch(`${CONFIG.geocode}?q=${encodeURIComponent(q)}`);
          renderSuggest(await r.json());}catch(e){closeSuggest();}
      },320);
    });
    $("place").addEventListener("keydown",(e)=>{
      if(!suggestBox.classList.contains("open"))return;
      const btns=[...suggestBox.querySelectorAll("button")];
      if(e.key==="ArrowDown"){e.preventDefault();suggestIndex=Math.min(suggestIndex+1,btns.length-1);}
      else if(e.key==="ArrowUp"){e.preventDefault();suggestIndex=Math.max(suggestIndex-1,0);}
      else if(e.key==="Enter"&&suggestIndex>=0){e.preventDefault();btns[suggestIndex].click();return;}
      else if(e.key==="Escape"){closeSuggest();return;}
      btns.forEach((b,i)=>b.classList.toggle("active",i===suggestIndex));
    });
    document.addEventListener("click",(e)=>{if(!e.target.closest(".field"))closeSuggest();});

    /* ----- map tools: measure / route / reachability / corridors ----- */
    let activeMode=null;
    let measurePts=[],measureLine=null,measureMarkers=[],measurePoly=null;
    let routePts=[],routeLayer=null,routeMarkers=[];
    let isoEdge=null,isoHull=null,centralityLayer=null;
    const modeBtns={measure:$("measureBtn"),route:$("routeBtn"),iso:$("isoBtn")};
    function fmtDist(m){return m>=1000?(m/1000).toFixed(2)+" km":Math.round(m)+" m";}
    function fmtArea(m2){return m2>=1e6?(m2/1e6).toFixed(2)+" km2":Math.round(m2)+" m2";}

    function clearTools(){
      [measureLine,measurePoly,routeLayer,isoEdge,isoHull,centralityLayer]
        .forEach(l=>{if(l)map.removeLayer(l);});
      measureMarkers.concat(routeMarkers).forEach(m=>map.removeLayer(m));
      measureLine=measurePoly=routeLayer=isoEdge=isoHull=centralityLayer=null;
      measureMarkers=[];routeMarkers=[];measurePts=[];routePts=[];
      if($("centralityBtn"))$("centralityBtn").classList.remove("on");
    }
    const TOOL_HINTS={measure:"Measure: click points on the map.",
      route:"Route: click an origin, then a destination.",
      iso:"Reach: click a point to map travel reach."};
    function setToolHint(text){const h=$("toolsHint");if(!h)return;
      if(text){h.textContent=text;h.classList.add("active");}
      else{h.textContent="Pick a tool, then click the map.";h.classList.remove("active");}}
    function setMode(name){
      if(wiMode)wiSetMode(null);   // tools and What-If are mutually exclusive
      activeMode=activeMode===name?null:name;
      Object.entries(modeBtns).forEach(([k,b])=>{if(b){const on=k===activeMode;
        b.classList.toggle("on",on);b.setAttribute("aria-pressed",String(on));}});
      map.getContainer().style.cursor=activeMode?"crosshair":"";
      setToolHint(activeMode?TOOL_HINTS[activeMode]:"");
      if(activeMode)setStatus(TOOL_HINTS[activeMode],"");
      else if(lastData)setStatus(`Analysis ready: ${lastData.stats.place}`,"");
    }
    map.on("click",(e)=>{
      if(wiMode){onWhatifClick(e);return;}
      if(activeMode==="measure")onMeasureClick(e);
      else if(activeMode==="route")onRouteClick(e);
      else if(activeMode==="iso")onIsoClick(e);
    });

    function onMeasureClick(e){
      measurePts.push(e.latlng);
      const mk=L.circleMarker(e.latlng,{radius:4,color:"#0f766e",fillColor:"#fff",fillOpacity:1,weight:2}).addTo(map);
      measureMarkers.push(mk);
      const ll=measurePts.map(p=>[p.lat,p.lng]);
      if(measureLine)map.removeLayer(measureLine);
      measureLine=L.polyline(ll,{color:"#0f766e",weight:3,dashArray:"6 5"}).addTo(map);
      let dist=0;for(let i=1;i<measurePts.length;i++)dist+=map.distance(measurePts[i-1],measurePts[i]);
      let area=0;
      if(measurePts.length>=3){
        if(measurePoly)map.removeLayer(measurePoly);
        measurePoly=L.polygon(ll,{color:"#0f766e",weight:1,fillColor:"#0f766e",fillOpacity:.12}).addTo(map);
        const R=6371000,rad=Math.PI/180;let s=0;
        for(let i=0;i<measurePts.length;i++){const a=measurePts[i],b=measurePts[(i+1)%measurePts.length];
          s+=(b.lng-a.lng)*rad*(2+Math.sin(a.lat*rad)+Math.sin(b.lat*rad));}
        area=Math.abs(s*R*R/2);
      }
      setStatus(`Measure: ${fmtDist(dist)}${area?` | area ${fmtArea(area)}`:""}`,"");
    }

    async function onRouteClick(e){
      if(routePts.length>=2){
        if(routeLayer)map.removeLayer(routeLayer);routeMarkers.forEach(m=>map.removeLayer(m));
        routeLayer=null;routeMarkers=[];routePts=[];
      }
      routePts.push(e.latlng);
      const label=routePts.length===1?"A":"B";
      const mk=L.circleMarker(e.latlng,{radius:7,color:"#fff",weight:2,fillColor:"#111827",fillOpacity:1})
        .bindTooltip(label,{permanent:true,direction:"top"}).addTo(map);
      routeMarkers.push(mk);
      if(routePts.length<2)return;
      setStatus("Computing shortest path...","busy");
      const[a,b]=routePts;
      try{
        const r=await fetch(`${CONFIG.route}?${baseParams({from_lat:a.lat,from_lon:a.lng,to_lat:b.lat,to_lon:b.lng})}`);
        const d=await r.json();if(!r.ok)throw new Error(d.error||"Route failed");
        if(routeLayer)map.removeLayer(routeLayer);
        routeLayer=L.geoJSON(d,{style:{color:"#111827",weight:5,opacity:.9}}).addTo(map);
        setStatus(`Route: ${d.properties.distance_km} km, about ${d.properties.time_min} min by ${$("network").value}.`,"");
      }catch(err){setStatus(err.message,"error");}
    }

    async function onIsoClick(e){
      setStatus("Mapping travel reach...","busy");
      try{
        const r=await fetch(`${CONFIG.isochrone}?${baseParams({lat:e.latlng.lat,lon:e.latlng.lng,minutes:$("isoMin").value})}`);
        const d=await r.json();if(!r.ok)throw new Error(d.error||"Reachability failed");
        if(isoEdge)map.removeLayer(isoEdge);if(isoHull)map.removeLayer(isoHull);
        if(d.hull)isoHull=L.geoJSON(d.hull,{style:{color:"#0284c7",weight:2,fillColor:"#0ea5e9",fillOpacity:.1,dashArray:"6 5"}}).addTo(map);
        isoEdge=L.geoJSON(d.edges,{style:{color:"#0284c7",weight:2,opacity:.7}}).addTo(map);
        setStatus(`Reach in ${d.stats.minutes} min: ${d.stats.reachable_km} km of streets at ${d.stats.speed_kmh} km/h.`,"");
      }catch(err){setStatus(err.message,"error");}
    }

    async function toggleCentrality(){
      if(centralityLayer){map.removeLayer(centralityLayer);centralityLayer=null;
        $("centralityBtn").classList.remove("on");
        if(lastData)setStatus(`Analysis ready: ${lastData.stats.place}`,"");return;}
      $("centralityBtn").classList.add("on");setStatus("Computing critical corridors...","busy");
      try{
        const r=await fetch(`${CONFIG.centrality}?${baseParams({})}`);
        const d=await r.json();if(!r.ok)throw new Error(d.error||"Centrality failed");
        centralityLayer=L.geoJSON(d,{style:f=>{const s=f.properties.score;
          return {color:`hsl(${Math.round(45-45*s)},92%,${Math.round(58-22*s)}%)`,weight:1.5+s*5,opacity:.9};}}).addTo(map);
        setStatus(`${d.features.length} highest-traffic corridors${d.sampled?" (approximate)":""} by betweenness centrality.`,"");
      }catch(err){setStatus(err.message,"error");$("centralityBtn").classList.remove("on");}
    }

    $("routeBtn").addEventListener("click",()=>setMode("route"));
    $("isoBtn").addEventListener("click",()=>setMode("iso"));
    $("measureBtn").addEventListener("click",()=>setMode("measure"));
    $("centralityBtn").addEventListener("click",toggleCentrality);
    $("clearToolsBtn").addEventListener("click",()=>{clearTools();activeMode=null;
      Object.values(modeBtns).forEach(b=>{if(b){b.classList.remove("on");b.setAttribute("aria-pressed","false");}});
      map.getContainer().style.cursor="";setToolHint("");
      setStatus(lastData?`Analysis ready: ${lastData.stats.place}`:"Cleared.","");});
    $("legendToggle").addEventListener("click",()=>{
      const hidden=$("legend").classList.toggle("hidden");
      $("legendToggle").setAttribute("aria-expanded",String(!hidden));});

    /* ----- export ----- */
    function download(name,text,type){
      const blob=new Blob([text],{type});const a=document.createElement("a");
      a.href=URL.createObjectURL(blob);a.download=name;a.click();URL.revokeObjectURL(a.href);
    }
    $("exportGeo").addEventListener("click",()=>{
      if(!lastData){setStatus("Run an analysis first.","error");return;}
      const fc={type:"FeatureCollection",features:[...lastData.geojson.features]};
      Object.values(lastData.pois.categories||{}).forEach(c=>fc.features.push(...c.geojson.features));
      download((lastData.stats.place||"gis").replace(/[^\w]+/g,"_")+".geojson",
        JSON.stringify(fc),"application/geo+json");
    });
    $("exportPng").addEventListener("click",()=>{
      if(!lastData){setStatus("Run an analysis first.","error");return;}
      if(typeof leafletImage!=="function"){setStatus("PNG export unavailable; use GeoJSON or print.","error");return;}
      setStatus("Rendering PNG...","busy");
      leafletImage(map,(err,canvas)=>{
        if(err){setStatus("PNG export failed (tile security). Use GeoJSON or print instead.","error");return;}
        const a=document.createElement("a");a.href=canvas.toDataURL("image/png");
        a.download=(lastData.stats.place||"gis").replace(/[^\w]+/g,"_")+".png";a.click();
        setStatus(`Analysis ready: ${lastData.stats.place}`,"");
      });
    });

    /* ----- wiring ----- */
    $("searchForm").addEventListener("submit",(e)=>{e.preventDefault();closeSuggest();analyze();});
    $("chips").addEventListener("click",(e)=>{const b=e.target.closest("[data-place]");
      if(!b)return;$("place").value=b.dataset.place;analyze();});
    $("locateButton").addEventListener("click",()=>{
      if(!navigator.geolocation){setStatus("Geolocation is not available.","error");return;}
      setStatus("Locating...","busy");
      navigator.geolocation.getCurrentPosition(
        (pos)=>{const{latitude,longitude}=pos.coords;
          $("place").value=`${latitude.toFixed(5)}, ${longitude.toFixed(5)}`;
          analyze({lat:latitude,lon:longitude});},
        ()=>setStatus("Could not get your location.","error"),{timeout:8000});
    });

    /* ----- What-If Studio ----- */
    function wiSetMode(mode){
      wiMode=(wiMode===mode)?null:mode;
      if(wiMode){activeMode=null;Object.values(modeBtns).forEach(b=>b&&b.classList.remove("on"));}
      $("wiAddBtn").classList.toggle("armed",wiMode==="add");
      $("wiCloseBtn").classList.toggle("armed",wiMode==="close");
      map.getContainer().style.cursor=wiMode?"crosshair":"";
      if(wiMode==="add")$("wiHint").textContent=`Click the map to place a ${$("wiCategory").selectedOptions[0].text.toLowerCase()}.`;
      else if(wiMode==="close")$("wiHint").textContent="Click the map to close streets around that point.";
      else if(!wiInterventions.length)$("wiHint").textContent="Pick a mode, then click the map to drop changes.";
    }
    function onWhatifClick(e){
      if(wiMode==="add"){
        const cat=$("wiCategory").value, label=$("wiCategory").selectedOptions[0].text;
        wiInterventions.push({type:"add",category:cat,lat:e.latlng.lat,lon:e.latlng.lng});
        wiMarkers.push(L.circleMarker(e.latlng,{radius:7,color:"#fff",weight:2,fillColor:"#12b76a",fillOpacity:1})
          .bindTooltip("+ "+label,{direction:"top"}).addTo(map));
      } else if(wiMode==="close"){
        wiInterventions.push({type:"close",lat:e.latlng.lat,lon:e.latlng.lng,radius:150});
        wiMarkers.push(L.circle(e.latlng,{radius:150,color:"#f04438",weight:2,fillColor:"#f04438",fillOpacity:.12})
          .bindTooltip("Closed area",{direction:"top"}).addTo(map));
      } else return;
      $("wiRun").disabled=false;$("wiReset").disabled=false;
      $("wiHint").textContent=`${wiInterventions.length} change${wiInterventions.length>1?"s":""} staged. Click Recompute.`;
    }
    async function wiRecompute(){
      if(!lastData||!wiInterventions.length)return;
      $("wiRun").disabled=true;setStatus("Recomputing walkability with your changes...","busy");
      try{
        const res=await fetch(CONFIG.whatif,{method:"POST",headers:{"Content-Type":"application/json"},
          body:JSON.stringify(Object.assign({},lastQuery,{interventions:wiInterventions}))});
        const d=await res.json();
        if(!res.ok)throw new Error(d.error||"Recompute failed");
        renderWhatif(d);setStatus("What-If result ready. Reset to restore the original.","");
      }catch(err){setStatus(err.message,"error");}
      finally{$("wiRun").disabled=false;}
    }
    function renderWhatif(d){
      if(walkZoneLayer){map.removeLayer(walkZoneLayer);walkZoneLayer=null;}
      if(wiZoneLayer){map.removeLayer(wiZoneLayer);wiZoneLayer=null;}
      if(wiClosedLayer){map.removeLayer(wiClosedLayer);wiClosedLayer=null;}
      if(d.new_access&&d.new_access.zone){
        wiZoneLayer=L.geoJSON(d.new_access.zone,{style:{color:"#7c3aed",weight:2,dashArray:"4 4",
          fillColor:"#7c3aed",fillOpacity:.08}}).addTo(map);
        wiZoneLayer.bringToBack();
      }
      if(d.removed_edges&&d.removed_edges.features.length){
        wiClosedLayer=L.geoJSON(d.removed_edges,{style:{color:"#f04438",weight:3,opacity:.9}}).addTo(map);
      }
      if(d.new_access)renderAccess(d.new_access);
      const dl=d.delta;
      if(!dl){$("wiResult").innerHTML="";return;}
      const s=dl.score_delta, cls=s>0?"up":s<0?"down":"flat", sign=s>0?"+":"";
      const rows=dl.categories.filter(c=>c.delta!==0).map(c=>
        `<div class="wi-row"><span>${c.label}</span><span class="${c.delta>0?'up':'down'}">${c.before} &rarr; ${c.after} (${c.delta>0?'+':''}${c.delta})</span></div>`).join("");
      $("wiResult").innerHTML=`<div class="wi-delta"><div class="big">Walk score ${dl.score_before} &rarr; <span class="${cls}">${dl.score_after} (${sign}${s})</span></div>${rows||'<div class="wi-row"><span>No category change within a 15-minute walk.</span></div>'}</div>`;
    }
    function wiResetAll(){
      wiInterventions=[];wiMarkers.forEach(m=>map.removeLayer(m));wiMarkers=[];
      if(wiZoneLayer){map.removeLayer(wiZoneLayer);wiZoneLayer=null;}
      if(wiClosedLayer){map.removeLayer(wiClosedLayer);wiClosedLayer=null;}
      wiSetMode(null);$("wiAddBtn").classList.remove("armed");$("wiCloseBtn").classList.remove("armed");
      $("wiRun").disabled=true;$("wiReset").disabled=true;$("wiResult").innerHTML="";
      $("wiHint").textContent="Pick a mode, then click the map to drop changes.";
      if(lastData){renderAccess(lastData.access);renderNetwork(lastData);}
    }
    $("wiAddBtn").addEventListener("click",()=>wiSetMode("add"));
    $("wiCloseBtn").addEventListener("click",()=>wiSetMode("close"));
    $("wiRun").addEventListener("click",wiRecompute);
    $("wiReset").addEventListener("click",wiResetAll);

    /* ----- Ask the City ----- */
    function escapeHtml(s){return s.replace(/&/g,"&amp;").replace(/</g,"&lt;").replace(/>/g,"&gt;");}
    function inlineMd(s){
      s=escapeHtml(s);
      s=s.replace(/\*\*(.+?)\*\*/g,"<strong>$1</strong>");
      s=s.replace(/(^|[^*])\*(?!\s)([^*]+?)\*(?!\*)/g,"$1<em>$2</em>");
      return s;
    }
    function renderMarkdown(text){
      const lines=(text||"").replace(/\r/g,"").split("\n");
      let html="", inList=false;
      const closeList=()=>{ if(inList){html+="</ul>";inList=false;} };
      for(const raw of lines){
        const line=raw.trim();
        if(!line){closeList();continue;}
        const li=line.match(/^[-*•]\s+(.*)$/);
        if(li){ if(!inList){html+="<ul>";inList=true;} html+="<li>"+inlineMd(li[1])+"</li>"; continue; }
        closeList();
        const h=line.match(/^#{1,4}\s+(.*)$/);
        html += h ? "<p class=\"h\">"+inlineMd(h[1])+"</p>" : "<p>"+inlineMd(line)+"</p>";
      }
      closeList();
      return html || "<p></p>";
    }
    async function askCity(q){
      const question=(q||$("askInput").value).trim();
      if(!question)return;
      const out=$("askAnswer");
      $("askBtn").disabled=true;out.classList.add("loading");out.textContent="Analysing this place...";
      try{
        const res=await fetch(CONFIG.ask,{method:"POST",headers:{"Content-Type":"application/json"},
          body:JSON.stringify(Object.assign({},lastQuery||{place:$("place").value.trim(),
            network:$("network").value,radius:$("radius").value},{question}))});
        const d=await res.json();
        if(!res.ok)throw new Error(d.error||"Ask failed");
        out.classList.remove("loading");out.innerHTML=renderMarkdown(d.answer);
      }catch(err){out.classList.remove("loading");out.textContent=err.message;}
      finally{$("askBtn").disabled=false;}
    }
    $("askBtn").addEventListener("click",()=>askCity());
    $("askInput").addEventListener("keydown",e=>{if(e.key==="Enter"){e.preventDefault();askCity();}});
    $("askChips").addEventListener("click",e=>{const b=e.target.closest("[data-q]");
      if(b){$("askInput").value=b.dataset.q;askCity(b.dataset.q);}});

    analyze();
  </script>
</body>
</html>
"""

# --------------------------------------------------------------------------- #
# App factory / entry point
# --------------------------------------------------------------------------- #

URL_PREFIX = os.environ.get("GIS_URL_PREFIX", "").rstrip("/")

app = Flask(__name__)
app.register_blueprint(gis, url_prefix=URL_PREFIX or None)
# Honour X-Forwarded-* headers so url_for() works behind a reverse proxy.
app.wsgi_app = ProxyFix(
    app.wsgi_app, x_for=1, x_proto=1, x_host=1, x_prefix=1
)


def main() -> None:
    from waitress import serve

    host = os.environ.get("GIS_HOST", "127.0.0.1")
    # PORT is the convention used by Render/Railway/Heroku-style hosts.
    port = int(os.environ.get("GIS_PORT") or os.environ.get("PORT") or "5006")
    mount = URL_PREFIX or "/"
    print(f"GeoPulse GIS serving on http://{host}:{port}{mount}")
    serve(app, host=host, port=port, threads=8)


if __name__ == "__main__":
    main()
