# Universal container image (Fly.io, Railway, Cloud Run, any container host).
FROM python:3.12-slim

WORKDIR /app
COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt
COPY gis.py .

# Mounted at /gis so every browser-facing URL carries the prefix the proxy
# forwards. GIS_HOST=0.0.0.0 lets the container accept external connections.
ENV GIS_URL_PREFIX=/gis \
    GIS_HOST=0.0.0.0 \
    PORT=8080

EXPOSE 8080
CMD ["python", "gis.py"]
