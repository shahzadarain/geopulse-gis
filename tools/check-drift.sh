#!/usr/bin/env bash
# gis.py lives in two places:
#
#   connect-canvas/gis.py   <- SOURCE OF TRUTH. Served live at shahzadasghar.com/gis
#                              via connect-canvas/api/index.py (vercel.json rewrites
#                              /gis -> /api/index, functions.includeFiles: "gis.py").
#   geopulse-gis/gis.py     <- standalone copy (Docker / Render / Procfile). Not
#                              currently deployed anywhere.
#
# They silently diverged once: the live copy gained Google Analytics, og:image, an
# SEO section, the accessibility widget and app.url_map.strict_slashes = False,
# while edits to this repo never reached production at all.
#
# Run this before editing either copy. Line endings are ignored: the live file has
# mixed LF/CRLF, so only content is compared.
#
#   ./tools/check-drift.sh          report only
#   ./tools/check-drift.sh --sync   overwrite this repo's copy from the live one
#
# Exit 0 = in sync, 1 = drifted, 2 = live copy not found.

set -u

LIVE="${CONNECT_CANVAS_GIS:-/d/shahzadwebsite/connect-canvas/gis.py}"
HERE="$(cd "$(dirname "$0")/.." && pwd)/gis.py"

if [ ! -f "$LIVE" ]; then
  echo "check-drift: live copy not found at $LIVE" >&2
  echo "             set CONNECT_CANVAS_GIS to its path" >&2
  exit 2
fi

tmp_live=$(mktemp); tmp_here=$(mktemp)
trap 'rm -f "$tmp_live" "$tmp_here"' EXIT
tr -d '\r' < "$LIVE" > "$tmp_live"
tr -d '\r' < "$HERE" > "$tmp_here"

if cmp -s "$tmp_live" "$tmp_here"; then
  echo "check-drift: in sync with $LIVE"
  exit 0
fi

if [ "${1:-}" = "--sync" ]; then
  cp "$tmp_live" "$HERE"
  echo "check-drift: synced this repo's gis.py from $LIVE"
  echo "             review with 'git diff' before committing."
  exit 0
fi

echo "check-drift: DRIFTED from $LIVE" >&2
echo >&2
diff -u "$tmp_here" "$tmp_live" | head -60 >&2
echo >&2
echo "  '-' = only here (geopulse)   '+' = only live (connect-canvas)" >&2
echo "  Edits belong in the live copy first. Then: ./tools/check-drift.sh --sync" >&2
exit 1
