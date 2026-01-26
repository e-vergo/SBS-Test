#!/bin/bash
# Build and serve the SBS-Test blueprint locally
# Usage: ./scripts/build_blueprint.sh
#
# This script uses the pure Lean blueprint pipeline (no Python/plasTeX):
#   1. Builds local dependency forks (SubVerso, LeanArchitect, Dress, Runway)
#   2. Fetches mathlib cache
#   3. Builds Lean project with BLUEPRINT_DRESS=1 (generates per-declaration artifacts)
#   4. Builds :blueprint Lake facet
#   5. Generates dependency graph via Dress extract_blueprint
#   6. Generates static site via Runway (reads dressed artifacts + runway.json)
#   7. Serves site locally at http://localhost:8000
#
# Configuration:
#   - runway.json: Site config (title, URLs, blueprintTexPath for chapter structure)
#   - blueprint/src/blueprint.tex: Chapter organization and prose content
#
# All dependencies use local paths for development. No git push/pull needed.

set -e

cd "$(dirname "$0")/.."
PROJECT_ROOT=$(pwd)

# Configuration - paths to local dependency forks
SUBVERSO_PATH="/Users/eric/GitHub/Side-By-Side-Blueprint/subverso"
LEAN_ARCHITECT_PATH="/Users/eric/GitHub/Side-By-Side-Blueprint/LeanArchitect"
DRESS_PATH="/Users/eric/GitHub/Side-By-Side-Blueprint/Dress"
RUNWAY_PATH="/Users/eric/GitHub/Side-By-Side-Blueprint/Runway"
DRESS_BLUEPRINT_ACTION_PATH="/Users/eric/GitHub/Side-By-Side-Blueprint/dress-blueprint-action"
SBSTest_PATH="/Users/eric/GitHub/Side-By-Side-Blueprint/SBS-Test"
SIDE_BY_SIDE_BLUEPRINT_PATH="/Users/eric/GitHub/Side-By-Side-Blueprint"



echo "=== SBS-Test Blueprint Builder ==="
echo ""

# Check dependencies
check_dependency() {
    if ! command -v "$1" &> /dev/null; then
        echo "ERROR: $1 is not installed."
        echo "$2"
        exit 1
    fi
}

check_dependency "lake" "Please install Lean 4 and Lake."

# Verify local paths exist
for path in "$SUBVERSO_PATH" "$LEAN_ARCHITECT_PATH" "$DRESS_PATH" "$RUNWAY_PATH" "$DRESS_BLUEPRINT_ACTION_PATH"; do
    if [[ ! -d "$path" ]]; then
        echo "ERROR: Dependency not found at $path"
        exit 1
    fi
done

# Kill any existing processes on port 8000
echo "Killing any existing servers on port 8000..."
lsof -ti:8000 | xargs kill -9 2>/dev/null || true

echo ""
echo "=== Step 0: Committing and pushing dependency changes ==="

# Function to commit and push changes in a repo
commit_and_push() {
    local repo_path="$1"
    local repo_name="$(basename "$repo_path")"

    cd "$repo_path"

    # Check if there are any changes to commit
    if [[ -n $(git status --porcelain) ]]; then
        echo "  $repo_name: Committing changes..."
        git add -A
        git commit -m "Auto-commit from build_blueprint.sh

Co-Authored-By: Claude Opus 4.5 <noreply@anthropic.com>"
        echo "  $repo_name: Pushing..."
        git push
        echo "  $repo_name: Done. Waiting 2 seconds..."
        sleep 2
    else
        echo "  $repo_name: No changes to commit"
    fi
}

commit_and_push "$SUBVERSO_PATH"
commit_and_push "$LEAN_ARCHITECT_PATH"
commit_and_push "$DRESS_PATH"
commit_and_push "$RUNWAY_PATH"
commit_and_push "$DRESS_BLUEPRINT_ACTION_PATH"
commit_and_push "$SBSTest_PATH"
commit_and_push "$SIDE_BY_SIDE_BLUEPRINT_PATH"

cd "$PROJECT_ROOT"

echo ""
echo "=== Step 1: Building local dependency forks ==="

# Build order: SubVerso -> LeanArchitect -> Dress -> Runway (respects dependency chain)

echo "Building SubVerso..."
(cd "$SUBVERSO_PATH" && lake build)

echo "Building LeanArchitect..."
(cd "$LEAN_ARCHITECT_PATH" && lake build)

echo "Building Dress..."
(cd "$DRESS_PATH" && lake build)

echo "Building Runway..."
(cd "$RUNWAY_PATH" && lake build)

echo ""
echo "=== Step 2: Fetching mathlib cache ==="
cd "$PROJECT_ROOT"
lake exe cache get || echo "Cache fetch completed (some files may have been skipped)"

echo ""
echo "=== Step 3: Building Lean project with dressed artifacts ==="
# Use BLUEPRINT_DRESS=1 environment variable to enable dressed artifact generation.
# Dress's ElabRules.lean checks this env var to generate per-declaration artifacts
# during elaboration.
#
# Clean build artifacts to force re-elaboration (cached oleans skip elab_rules).
rm -rf "$PROJECT_ROOT/.lake/build/lib/SBSTest"
rm -rf "$PROJECT_ROOT/.lake/build/ir/SBSTest"
rm -rf "$PROJECT_ROOT/.lake/build/dressed"

BLUEPRINT_DRESS=1 lake build

echo ""
echo "=== Step 4: Building blueprint facet ==="
lake build :blueprint

echo ""
echo "=== Step 5: Generating dependency graph ==="
# Run extract_blueprint graph command from local Dress
# Uses lake env to ensure correct LEAN_PATH for importing project modules
lake env "$DRESS_PATH/.lake/build/bin/extract_blueprint" graph \
    --build "$PROJECT_ROOT/.lake/build" \
    SBSTest

echo ""
echo "=== Step 6: Generating site with Runway ==="
# Runway reads:
#   - Dress artifacts from .lake/build/dressed/
#   - Configuration from runway.json (includes blueprintTexPath for chapter structure)
# Outputs to .lake/build/runway/
OUTPUT_DIR="$PROJECT_ROOT/.lake/build/runway"
rm -rf "$OUTPUT_DIR"

# Verify runway.json exists
if [[ ! -f "$PROJECT_ROOT/runway.json" ]]; then
    echo "ERROR: runway.json not found. Create it with blueprintTexPath set."
    exit 1
fi

(cd "$RUNWAY_PATH" && lake exe runway \
    --build-dir "$PROJECT_ROOT/.lake/build" \
    --output "$OUTPUT_DIR" \
    build \
    "$PROJECT_ROOT/runway.json")

echo ""
echo "=== Blueprint ready ==="
echo "  Output: $OUTPUT_DIR"
echo "  Web: http://localhost:8000"
echo ""

# Start server in background
python3 -m http.server -d "$OUTPUT_DIR" 8000 &
SERVER_PID=$!
echo "Server started (PID: $SERVER_PID)"

# Open browser
(sleep 1 && open "http://localhost:8000") &

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
