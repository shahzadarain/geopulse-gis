# GeoPulse GIS

Live street-network and points-of-interest analysis for any place on Earth.
A single-file Flask application that builds a real street graph and a real POI
layer from OpenStreetMap (Overpass API), geocodes with Nominatim, and computes
every metric it shows directly from the returned data.

## Features

- Search any country, city, place name, or `lat, lon` (with type-ahead
  suggestions via Nominatim) and "Use my location".
- Real street network per travel mode (drive / walk / bike / all paths) with
  per-road-type colouring and hover/popup detail.
- Real points of interest in six toggleable categories (healthcare, education,
  food & retail, transit & fuel, civic & finance, parks & leisure).
- Computed metrics: street segments, intersections, total length, street
  density (km/km2), a transparent connectivity index, circuity, dead-end ratio,
  road-class mix, and a length-weighted street-orientation rose with a
  grid-order index.
- Graph analytics on the live network:
  - **Route** - shortest path (Dijkstra, weighted by length) between any two
    clicked points, with distance and an estimated travel time per mode.
  - **Reach** - travel-time reachability ("isochrone"): the streets and the
    boundary you can reach within N minutes from a clicked point.
  - **Corridors** - edge betweenness centrality, highlighting the streets that
    carry the most shortest paths (exact for small graphs, sampled for large).
- Measure tool (distance and area), GeoJSON export of the full result, and a
  best-effort PNG snapshot of the map.
- Light / dark / OpenStreetMap basemaps, responsive layout, loading and error
  states.

All analysis is derived from the data actually returned by OpenStreetMap. The
connectivity index is a clearly labelled heuristic blend of intersection
density and street continuity, not a measured field. If every Overpass mirror
is unreachable, the app shows a small sample grid that is explicitly labelled
"sample data" rather than presenting placeholder values as real.

No `osmnx` or `geopandas` is required - data is fetched directly over HTTP.

## Run locally

```bash
pip install -r requirements.txt
python gis.py
# open http://127.0.0.1:5006/
```

Environment variables (see `.env.example`): `GIS_HOST`, `GIS_PORT`,
`GIS_URL_PREFIX`, `GIS_OVERPASS_URL`, `GIS_NOMINATIM_URL`.

## Production server

The app uses [waitress](https://github.com/Pylons/waitress) (works on Windows
and Linux). Run it directly:

```bash
python gis.py
```

or with the waitress CLI:

```bash
# Windows (PowerShell)
$env:GIS_URL_PREFIX="/gis"
waitress-serve --listen=127.0.0.1:5006 gis:app
```

## Hosting at https://shahzadasghar.org/gis

The main site (`connect-canvas`) is a Vite/React SPA on **Vercel** with Supabase
Edge Functions - there is no Python runtime there. This Flask app therefore runs
on a small **separate Python host**, and Vercel proxies `/gis` to it. Because the
proxy is server-side, the browser sees one origin (no CORS), and the backend
stays mounted at `/gis` so every generated URL carries the prefix Vercel forwards.

### Step 1 - deploy the backend to a Python host

Push this folder to a GitHub repo, then pick one:

- **Render** (simplest): "New > Blueprint" against the repo; `render.yaml` is
  included. It comes up at `https://<name>.onrender.com/gis/`. Use the
  **starter** plan (always-on) for a live demo - the free plan sleeps after
  ~15 min idle and cold-starts in ~30-50s.
- **Railway / Fly.io / Cloud Run**: use the included `Dockerfile`.
- **Any VPS**: `GIS_URL_PREFIX=/gis waitress-serve --listen=*:5006 gis:app`
  behind your own proxy (see `Procfile`).

Set `GIS_URL_PREFIX=/gis` on the host (the blueprint and Dockerfile already do).
Verify `https://<backend-host>/gis/healthz` returns `{"status":"ok"}`.

### Step 2 - point Vercel `/gis` at the backend

Edit `connect-canvas/vercel.json` and add the two `/gis` rewrites **above** the
existing SPA catch-all (order matters - the catch-all otherwise swallows `/gis`).
See `vercel-rewrite.example.json`; replace `BACKEND_HOST`:

```json
"rewrites": [
  { "source": "/gis",     "destination": "https://BACKEND_HOST/gis" },
  { "source": "/gis/(.*)", "destination": "https://BACKEND_HOST/gis/$1" },
  { "source": "/(.*)",     "destination": "/index.html" }
]
```

Redeploy the Vercel site. `https://shahzadasghar.org/gis` now serves the tool.

## Endpoints

| Method | Path                | Purpose                                   |
| ------ | ------------------- | ----------------------------------------- |
| GET    | `/`                 | The single-page application               |
| GET    | `/api/network`      | Street network + POIs + stats + rose      |
| GET    | `/api/route`        | Shortest path between two points          |
| GET    | `/api/isochrone`    | Travel-time reachability from a point     |
| GET    | `/api/centrality`   | Edge betweenness of the street network    |
| GET    | `/api/geocode?q=`   | Nominatim type-ahead suggestions          |
| GET    | `/healthz`          | Health check                              |

`/api/network` accepts `place` (or `lat`+`lon`), `network`
(`drive|walk|bike|all`), and `radius` (metres, 400-10000). The analytics
endpoints take the same `place`/`network`/`radius` (so they reuse the cached
graph) plus their own points: `route` needs `from_lat,from_lon,to_lat,to_lon`;
`isochrone` needs `lat,lon,minutes`.

## Attribution

Map data and points of interest (C) OpenStreetMap contributors, available under
the Open Database License (ODbL). Basemap tiles by CARTO and OpenStreetMap.
