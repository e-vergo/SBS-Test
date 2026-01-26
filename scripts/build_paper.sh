#!/bin/bash
# Build and serve the paper locally (fast mode - uses existing artifacts)
# Usage: ./scripts/build_paper.sh
#
# Prerequisites: Run ./scripts/build_blueprint.sh first to generate artifacts.
#
# This script:
#   1. Builds Runway if needed
#   2. Generates paper.html from existing dressed artifacts
#   3. Serves at http://localhost:8000/paper.html
#   4. Auto-exits after 5 minutes

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

# Kill any existing processes on port 8000
echo "Killing any existing servers on port 8000..."
lsof -ti:8000 | xargs kill -9 2>/dev/null || true

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
echo "=== Paper ready ==="
echo "  Output: $OUTPUT_DIR/paper.html"
echo "  Web: http://localhost:8000/paper.html"
echo ""

# Start server in background
cd "$OUTPUT_DIR"
python3 -m http.server 8000 &
SERVER_PID=$!
echo "Server started (PID: $SERVER_PID)"

# Open browser
(sleep 1 && open "http://localhost:8000/paper.html") &

echo ""
echo "=== BUILD COMPLETE ==="
echo "Server running at http://localhost:8000 (PID: $SERVER_PID)"
echo "Server will auto-exit in 5 minutes..."
echo ""

# Auto-exit after 5 minutes with graceful offset
# Wait 297 seconds, print warning, then kill at 300 seconds
sleep 297
echo "Server shutting down in 3 seconds..."
sleep 3
kill $SERVER_PID 2>/dev/null
echo "Server stopped. Build script complete."
exit 0
