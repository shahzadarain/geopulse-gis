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
DEFAULT_PLACE = "Amman, Jordan"
HTTP_TIMEOUT = 90
MAX_POIS = 1500
USER_AGENT = "GeoPulseGIS/2.0 (https://shahzadasghar.org/gis)"
ORIENTATION_BINS = 36  # 10-degree bins for the street-orientation rose

# Typical travel speeds (metres/second) used for routing time and isochrones.
SPEED_MPS = {"drive": 11.1, "bike": 4.2, "walk": 1.4, "all": 1.4}

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


@lru_cache(maxsize=256)
def geocode_place(place: str) -> tuple[float, float, str]:
    """Resolve a place name (or 'lat,lon') to (lat, lon, display_name)."""
    coords = parse_latlon(place)
    if coords:
        lat, lon = coords
        return lat, lon, f"{lat:.4f}, {lon:.4f}"

    fallback = FALLBACK_LOCATIONS.get(place.strip().lower())

    try:
        response = _session.get(
            f"{NOMINATIM_URL}/search",
            params={"q": place, "format": "jsonv2", "limit": 1},
            timeout=HTTP_TIMEOUT,
        )
        response.raise_for_status()
        results = response.json()
        if results:
            top = results[0]
            return (
                float(top["lat"]),
                float(top["lon"]),
                top.get("display_name", place),
            )
    except Exception:  # noqa: BLE001 - fall back to the offline table
        pass

    if fallback:
        return fallback[0], fallback[1], place
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
    k = None if n <= 250 else min(200, n - 1)
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


@lru_cache(maxsize=64)
def analyze(place: str, network_type: str, radius_m: int) -> dict[str, Any]:
    lat, lon, display_name = geocode_place(place)
    label = display_name if display_name else place

    try:
        with ThreadPoolExecutor(max_workers=2) as pool:
            streets_future = pool.submit(
                fetch_streets, lat, lon, radius_m, network_type
            )
            pois_future = pool.submit(fetch_pois, lat, lon, radius_m)
            raw_streets = streets_future.result()
            raw_pois = pois_future.result()
        result = build_street_network(
            raw_streets, label, lat, lon, radius_m, network_type,
            "OpenStreetMap (Overpass live)",
        )
        pois = build_pois(raw_pois)
    except RuntimeError:
        result = build_demo_network(label, network_type, radius_m, lat, lon)
        pois = {"categories": {}, "total": 0, "shown": 0, "capped": False}

    result["pois"] = pois
    result["insights"] = build_insights(result["stats"], pois)
    return result


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
    }
    html = PAGE.replace("__GIS_CONFIG__", json.dumps(config))
    return Response(html, mimetype="text/html")


@gis.get("/healthz")
def healthz() -> Any:
    return jsonify({"status": "ok"})


@gis.get("/api/geocode")
def geocode() -> Any:
    query = request.args.get("q", "").strip()
    if len(query) < 2:
        return jsonify([])
    try:
        response = _session.get(
            f"{NOMINATIM_URL}/search",
            params={"q": query, "format": "jsonv2", "limit": 6},
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
    radius_raw = request.args.get("radius", "3000")

    if not place:
        return jsonify({"error": "Enter a country, city, or place name."}), 400
    if network_type not in NETWORK_TYPES:
        return jsonify({"error": "Choose drive, walk, bike, or all."}), 400

    try:
        radius_m = min(max(int(radius_raw), MIN_RADIUS_METERS), MAX_RADIUS_METERS)
    except ValueError:
        return jsonify({"error": "Radius must be a number."}), 400

    try:
        result = analyze(place, network_type, radius_m)
        public = {k: v for k, v in result.items() if not k.startswith("_")}
        return jsonify(public)
    except Exception as exc:  # noqa: BLE001
        return jsonify({"error": str(exc)}), 502


def _load_graph() -> tuple[nx.Graph, dict, str]:
    """Resolve the cached analysis for the request's place/network/radius."""
    place = request.args.get("place", DEFAULT_PLACE).strip()
    network_type = request.args.get("network", "drive").strip().lower()
    if network_type not in NETWORK_TYPES:
        network_type = "drive"
    try:
        radius_m = min(max(int(request.args.get("radius", "3000")),
                           MIN_RADIUS_METERS), MAX_RADIUS_METERS)
    except ValueError:
        radius_m = 3000
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
        return jsonify({"error": str(exc)}), 502


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
        return jsonify({"error": str(exc)}), 502


@gis.get("/api/centrality")
def centrality() -> Any:
    try:
        graph, nodes, _ = _load_graph()
        return jsonify(compute_centrality(graph, nodes))
    except Exception as exc:  # noqa: BLE001
        return jsonify({"error": str(exc)}), 502


# --------------------------------------------------------------------------- #
# Frontend (single page; __GIS_CONFIG__ is replaced at request time)
# --------------------------------------------------------------------------- #

PAGE = r"""<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>GeoPulse GIS</title>
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
    main{position:relative;min-width:0;height:100vh}
    #map{position:absolute;inset:0;background:#e8eef6}
    .map-card{position:absolute;z-index:500;right:18px;top:18px;width:min(420px,calc(100% - 36px));
      padding:12px 14px;background:var(--panel);border:1px solid var(--line);border-radius:8px;
      box-shadow:0 12px 30px rgba(16,24,40,.14)}
    .map-card strong{display:block;font-size:16px}
    .map-card span{display:block;margin-top:4px;color:var(--muted);font-size:13px;line-height:1.35}
    .status{position:absolute;z-index:700;left:50%;bottom:24px;max-width:min(620px,calc(100% - 48px));
      padding:10px 12px;color:#344054;background:#fff;border:1px solid var(--line);border-radius:8px;
      box-shadow:0 10px 25px rgba(16,24,40,.12);transform:translateX(-50%);font-size:13px}
    .status.error{color:#7a271a;background:#fff4ed;border-color:#f9dbaf}
    .status.busy::after{content:"";display:inline-block;width:12px;height:12px;margin-left:8px;
      vertical-align:-2px;border:2px solid #cfd6e4;border-top-color:var(--accent);
      border-radius:50%;animation:spin .8s linear infinite}
    @keyframes spin{to{transform:rotate(360deg)}}
    .tools{position:absolute;z-index:600;left:18px;top:18px;display:flex;gap:8px;flex-wrap:wrap}
    .tools button{width:auto;min-height:40px;padding:0 12px;background:#fff;color:#344054;
      border:1px solid var(--line);border-radius:8px;font-size:13px;font-weight:700;cursor:pointer;
      box-shadow:0 6px 18px rgba(16,24,40,.1)}
    .tools button.on{background:var(--accent);color:#fff;border-color:var(--accent)}
    .tools select{width:auto;min-height:40px;padding:0 8px;background:#fff;color:#344054;
      border:1px solid var(--line);border-radius:8px;font-size:13px;font-weight:700;
      box-shadow:0 6px 18px rgba(16,24,40,.1)}
    .legend{display:flex;flex-wrap:wrap;gap:6px 14px;margin-top:10px;font-size:12px;color:#475467}
    .legend i{display:inline-block;width:16px;height:6px;margin-right:6px;border-radius:99px;vertical-align:2px}
    @media (max-width:900px){
      body{overflow:auto}
      .shell{display:block;height:auto}
      aside{height:auto;border-right:0;border-bottom:1px solid var(--line)}
      main{height:72vh;min-height:520px}
      .map-card{left:12px;right:12px;top:12px;width:auto}
      .tools{top:auto;bottom:70px;left:12px}
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
          <input id="place" name="place" value="Amman, Jordan"
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
              <option value="1500">1.5 km</option>
              <option value="3000" selected>3 km</option>
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
          <button class="chip" type="button" data-place="Dubai, United Arab Emirates">Dubai</button>
          <button class="chip" type="button" data-place="San Francisco, California">San Francisco</button>
          <button class="chip" type="button" data-place="Tokyo, Japan">Tokyo</button>
          <button class="chip" type="button" data-place="Riyadh, Saudi Arabia">Riyadh</button>
          <button class="chip" type="button" data-place="London, United Kingdom">London</button>
        </div>
      </form>

      <section class="stats" aria-label="Network statistics">
        <div class="metric"><span>Street segments</span><strong id="m-edges">-</strong></div>
        <div class="metric"><span>Intersections</span><strong id="m-int">-</strong></div>
        <div class="metric"><span>Total length</span><strong id="m-len">-</strong></div>
        <div class="metric"><span>Density</span><strong id="m-den">-</strong></div>
        <div class="metric"><span>Connectivity index</span><strong id="m-conn">-</strong></div>
        <div class="metric"><span>Points of interest</span><strong id="m-poi">-</strong></div>
      </section>

      <section class="card">
        <h2>Road mix</h2>
        <div id="roadMix"></div>
      </section>

      <section class="card">
        <h2>Street orientation</h2>
        <canvas id="rose" width="320" height="320"
          style="display:block;margin:0 auto;width:100%;max-width:260px"></canvas>
        <p class="subtitle" id="roseNote" style="text-align:center;margin-top:6px"></p>
      </section>

      <section class="card">
        <h2>Points of interest</h2>
        <div id="poiToggles"></div>
      </section>

      <section class="card">
        <h2>Analysis</h2>
        <p class="subtitle" id="insightLead">Run an analysis to compute network
          structure and nearby services.</p>
        <div id="decisions"></div>
      </section>

      <section class="card">
        <h2>Export</h2>
        <div class="grid">
          <button class="ghost" type="button" id="exportGeo">GeoJSON</button>
          <button class="ghost" type="button" id="exportPng">PNG image</button>
        </div>
        <p class="subtitle" style="margin-top:10px">Data &copy; OpenStreetMap
          contributors (ODbL). Metrics are computed from the returned data.</p>
      </section>
    </aside>

    <main>
      <div id="map"></div>
      <div class="tools">
        <button type="button" id="routeBtn" title="Shortest path between two points">Route</button>
        <button type="button" id="isoBtn" title="Travel reach from a point">Reach</button>
        <select id="isoMin" title="Reach time" aria-label="Reach minutes">
          <option value="5">5 min</option>
          <option value="10" selected>10 min</option>
          <option value="15">15 min</option>
          <option value="20">20 min</option>
          <option value="30">30 min</option>
        </select>
        <button type="button" id="centralityBtn" title="Highest-traffic corridors">Corridors</button>
        <button type="button" id="measureBtn" title="Measure distance and area">Measure</button>
        <button type="button" id="clearToolsBtn" title="Clear overlays">Clear</button>
      </div>
      <div class="map-card">
        <strong id="mapTitle">Ready for analysis</strong>
        <span id="mapSubtitle">A fresh street graph is built from OpenStreetMap for the selected location.</span>
        <div class="legend" id="legend"></div>
      </div>
      <div id="status" class="status">Loading Amman as the opening example...</div>
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
    const POI_COLORS = {healthcare:"#e11d48",education:"#7c3aed",food_retail:"#d97706",
      transit:"#2563eb",civic:"#0f766e",leisure:"#16a34a"};

    const map = L.map("map",{preferCanvas:true,zoomControl:true}).setView([31.95,35.93],12);
    const light = L.tileLayer("https://{s}.basemaps.cartocdn.com/light_all/{z}/{x}/{y}{r}.png",
      {maxZoom:20,crossOrigin:true,attribution:"&copy; OpenStreetMap contributors &copy; CARTO"}).addTo(map);
    const dark = L.tileLayer("https://{s}.basemaps.cartocdn.com/dark_all/{z}/{x}/{y}{r}.png",
      {maxZoom:20,crossOrigin:true,attribution:"&copy; OpenStreetMap contributors &copy; CARTO"});
    const osm = L.tileLayer("https://tile.openstreetmap.org/{z}/{x}/{y}.png",
      {maxZoom:19,crossOrigin:true,attribution:"&copy; OpenStreetMap contributors"});
    L.control.layers({"Light":light,"Dark":dark,"OpenStreetMap":osm},{},{collapsed:true}).addTo(map);

    let streetLayer=null, haloLayer=null, lastData=null;
    let poiLayers={};

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

      try{map.fitBounds(data.bounds,{padding:[28,28]});}catch(e){}
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
      $("legend").innerHTML=
        '<span><i style="background:#d97706"></i>Roads</span>'+
        Object.entries(POI_COLORS).map(([k,c])=>
          `<span><i style="background:${c}"></i>${(lastData.pois.categories[k]||{}).label||k}</span>`).join("");
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
        renderRose(data.orientation||{});
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
    function setMode(name){
      activeMode=activeMode===name?null:name;
      Object.entries(modeBtns).forEach(([k,b])=>b&&b.classList.toggle("on",k===activeMode));
      map.getContainer().style.cursor=activeMode?"crosshair":"";
      if(activeMode==="measure")setStatus("Measure: click points on the map.","");
      else if(activeMode==="route")setStatus("Route: click an origin, then a destination.","");
      else if(activeMode==="iso")setStatus("Reach: click a point to map travel reach.","");
      else if(lastData)setStatus(`Analysis ready: ${lastData.stats.place}`,"");
    }
    map.on("click",(e)=>{
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
      Object.values(modeBtns).forEach(b=>b&&b.classList.remove("on"));
      map.getContainer().style.cursor="";
      setStatus(lastData?`Analysis ready: ${lastData.stats.place}`:"Cleared.","");});

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
