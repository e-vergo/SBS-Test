#!/bin/bash
set -e

PROJECT_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
RUNWAY_ROOT="$(cd "$PROJECT_ROOT/../Runway" && pwd)"
BUILD_DIR="$PROJECT_ROOT/.lake/build"
OUTPUT_DIR="$BUILD_DIR/runway"

echo "=== PAPER GENERATION (fast mode) ==="
echo "Project: $PROJECT_ROOT"
echo "Output: $OUTPUT_DIR"
echo ""

# Check artifacts exist
if [ ! -d "$BUILD_DIR/dressed" ]; then
  echo "Error: No dressed artifacts found at $BUILD_DIR/dressed"
  echo "Run ./scripts/build_blueprint.sh first to generate artifacts."
  exit 1
fi

# Build Runway if needed
echo "Building Runway..."
cd "$RUNWAY_ROOT"
lake build runway 2>&1 | tail -5

# Generate paper only (no Lean build, no artifact generation)
echo ""
echo "Generating paper..."
lake exe runway paper \
  --build-dir "$BUILD_DIR" \
  --output "$OUTPUT_DIR" \
  "$PROJECT_ROOT/runway.json"

echo ""
echo "Paper generated: $OUTPUT_DIR/paper.html"

# Optionally serve
if [ "$1" == "--serve" ]; then
  echo ""
  echo "Starting server..."
  cd "$OUTPUT_DIR"
  python3 -m http.server 8000 &
  SERVER_PID=$!
  sleep 1 && open "http://localhost:8000/paper.html"
  echo "Server running at http://localhost:8000 (Ctrl+C to stop)"
  echo "PID: $SERVER_PID"

  # Wait for Ctrl+C
  trap "kill $SERVER_PID 2>/dev/null; exit 0" INT
  wait $SERVER_PID
fi
