"""Vercel Python serverless entry point for the GeoPulse GIS Flask app.

Vercel serves the module-level WSGI ``app``. The app is mounted under /gis;
the prefix is set in the environment before importing gis.py, which reads it
at import time, so no Vercel env-var configuration is required.
"""

import os
import sys
from pathlib import Path

os.environ.setdefault("GIS_URL_PREFIX", "/gis")
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from gis import app  # noqa: E402  - Vercel serves this WSGI application
