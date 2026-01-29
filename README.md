# SBS-Test

Minimal test project for fast iteration during Side-by-Side Blueprint toolchain development.

## Purpose

SBS-Test serves three primary functions:

1. **Fast iteration testing** - Builds in ~2 minutes vs. ~30+ minutes for production projects (GCR, PNT). Use this for testing toolchain changes before validating on larger codebases.

2. **Feature demonstration** - Contains examples of every `@[blueprint]` attribute option, all 8 node statuses, and all dashboard features.

3. **Validation test fixtures** - Includes intentional test cases for:
   - Disconnected nodes (connectivity check)
   - Dependency cycles (cycle detection)
   - LaTeX-only entries (status display)

## Quick Start

**Option 1: Full build script** (recommended)
```bash
cd /Users/eric/GitHub/Side-By-Side-Blueprint/SBS-Test
./scripts/build_blueprint.sh
# Opens localhost:8000 when complete
```

**Option 2: Manual steps**
```bash
lake exe cache get
BLUEPRINT_DRESS=1 lake build
lake build :blueprint
cd ../Runway && lake exe runway build ../SBS-Test/runway.json
# Then: python3 -m http.server 8000 --directory .lake/build/runway
```

## Project Structure

```
SBS-Test/
├── SBSTest/
│   ├── Chapter1/
│   │   ├── Definitions.lean    # Basic definitions, term-mode proofs
│   │   └── Lemmas.lean         # Tactic-mode proofs
│   ├── Chapter2/
│   │   └── Theorems.lean       # Integer theorems, cross-chapter deps
│   ├── Chapter3/
│   │   └── Advanced.lean       # Prime numbers, deep dependency chains
│   ├── Chapter4/
│   │   └── StatusTest.lean     # All 8 statuses, dashboard features
│   └── TestChecks.lean         # Validation test fixtures (cycles, disconnected)
├── blueprint/
│   └── src/
│       ├── blueprint.tex       # Main LaTeX blueprint
│       └── paper.tex           # Paper generation test
├── runway.json                 # Site configuration
├── lakefile.toml               # Lake project config
└── scripts/
    └── build_blueprint.sh      # Full build script
```

## Blueprint Annotations

### Basic usage

```lean
@[blueprint "label"]
theorem simple_example : 1 + 1 = 2 := rfl
```

### With LaTeX statement and proof

```lean
@[blueprint "thm:succ-positive"
  (statement := /-- For any $n \in \mathbb{N}$, $n + 1 > 0$.
  \uses{def:is-positive} -/)
  (uses := ["def:is-positive"])
  (proof := /-- Direct application of successor properties. -/)]
theorem succ_positive (n : ℕ) : isPositive (n + 1) := Nat.succ_pos n
```

### Dashboard features

```lean
-- Key theorem (appears in Key Theorems panel)
@[blueprint "thm:main" (keyDeclaration := true)]

-- User message (appears in Messages panel)
@[blueprint "lem:helper" (message := "Consider alternative proof approach")]

-- Priority item (appears in Attention column)
@[blueprint "thm:urgent" (priorityItem := true)]

-- Project notes (appear in Project Notes panel)
@[blueprint "thm:blocked" (blocked := "Waiting for upstream mathlib PR")]
@[blueprint "lem:issue" (potentialIssue := "May not generalize to infinite case")]
@[blueprint "def:debt" (technicalDebt := "Refactor to use Finset API")]
@[blueprint "thm:misc" (misc := "See discussion in issue #42")]
```

### Status overrides

```lean
-- Manual status flags
@[blueprint "def:even" (mathlib := true)]           -- Already in Mathlib (dark blue)
@[blueprint "def:odd" (mathlibReady := true)]       -- Ready to upstream (medium blue)
@[blueprint "thm:alt" (ready := true)]              -- Ready to formalize (teal)
@[blueprint "thm:future" (notReady := true)]        -- Not ready (gray)
@[blueprint "thm:done" (fullyProven := true)]       -- Fully proven override (dark green)

-- Custom display name
@[blueprint "thm:square-nonneg" (title := "Squares are Non-negative")]
```

## Test Fixtures

### Cycle detection (`TestChecks.lean`)

Two declarations form an intentional dependency cycle:

```lean
@[blueprint "thm:cycleA" (uses := ["thm:cycleB"])]
theorem cycleA : True := trivial

@[blueprint "thm:cycleB" (uses := ["thm:cycleA"])]
theorem cycleB : True := trivial
```

The validation check should detect and report this cycle.

### Disconnected component (`TestChecks.lean`)

A declaration with no connections to the main graph:

```lean
@[blueprint "thm:disconnected"]
theorem disconnectedTheorem : 1 + 1 = 2 := rfl
```

The connectivity check should identify this as a separate component.

### LaTeX-only entry (`blueprint.tex`)

A theorem defined only in LaTeX (no Lean implementation):

```latex
\begin{theorem}[Parity Classification]
\label{thm:parity-classification}
\uses{def:even, def:odd}
Every natural number is either even or odd, but not both.
\end{theorem}
```

Should appear as "stated" (yellow) in the dependency graph.

## 8-Status Color Model

All statuses are demonstrated in `Chapter4/StatusTest.lean`:

| Status | Color | Meaning | Example |
|--------|-------|---------|---------|
| `inMathlib` | Dark blue (#1e3a5f) | Already in Mathlib | `def:even` |
| `mathlibReady` | Medium blue (#4a90d9) | Ready to upstream | `def:odd` |
| `fullyProven` | Dark green (#2e7d32) | This + all deps proven | `thm:zero-even` |
| `proven` | Green (#4caf50) | Formalized without sorry | `thm:even-add-even` |
| `sorry` | Orange (#ff9800) | Contains sorry | `thm:odd-add-odd` |
| `ready` | Teal (#26a69a) | Ready to formalize | `thm:alternating-parity` |
| `stated` | Yellow (#ffeb3b) | Blueprint only, no Lean | `thm:parity-classification` |
| `notReady` | Gray (#9e9e9e) | Not ready yet | `thm:goal-parity` |

## Testing Checklist

After toolchain changes, verify:

- [ ] **Build completes** - No errors from `build_blueprint.sh`
- [ ] **Site loads** - `index.html` opens without errors
- [ ] **Side-by-side display** - LaTeX left, Lean right
- [ ] **Proof toggles** - Both LaTeX and Lean proofs expand/collapse
- [ ] **Hover tooltips** - Type information on Lean tokens
- [ ] **Dependency graph** - Renders with correct layout
- [ ] **Node colors** - Match status (see 8-status table above)
- [ ] **Modal popups** - Click nodes to see side-by-side content
- [ ] **Pan/zoom** - Drag to pan, wheel to zoom, Fit button works
- [ ] **Dashboard stats** - Numbers reflect actual counts
- [ ] **Key Theorems** - Shows `keyDeclaration := true` items
- [ ] **Messages panel** - Shows `message := "..."` notes
- [ ] **Project Notes** - Shows blocked/issues/debt/misc
- [ ] **Validation results** - manifest.json contains checkResults
- [ ] **Paper generation** - `paper.html` and `paper.pdf` generated (if configured)

## Output Locations

After building:

| Path | Contents |
|------|----------|
| `.lake/build/dressed/` | Per-declaration artifacts (tex, html, json) |
| `.lake/build/runway/` | Generated site |
| `.lake/build/runway/index.html` | Dashboard homepage |
| `.lake/build/runway/dep_graph.html` | Dependency graph |
| `.lake/build/runway/manifest.json` | Precomputed stats + validation |
| `.lake/build/runway/paper.html` | Paper (MathJax) |
| `.lake/build/runway/paper.pdf` | Paper (PDF) |
| `.lake/build/runway/pdf.html` | PDF viewer |

## Configuration

`runway.json`:
```json
{
  "title": "SBS-Test: Blueprint Feature Demonstration",
  "projectName": "SBSTest",
  "githubUrl": "https://github.com/e-vergo/SBS-Test",
  "baseUrl": "/SBS-Test/",
  "blueprintTexPath": "blueprint/src/blueprint.tex",
  "assetsDir": "../dress-blueprint-action/assets",
  "paperTexPath": "blueprint/src/paper.tex",
  "paperTitle": "ar5iv Paper Demo",
  "paperAuthors": ["Side-By-Side Blueprint Project"],
  "paperAbstract": "A demonstration of ar5iv-style paper generation..."
}
```

`lakefile.toml`:
```toml
name = "SBSTest"

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "v4.27.0"

[[require]]
name = "Dress"
git = "https://github.com/e-vergo/Dress.git"
rev = "main"

[[lean_lib]]
name = "SBSTest"
```

## Links

- [Live Blueprint](https://e-vergo.github.io/SBS-Test/)
- [dress-blueprint-action](https://github.com/e-vergo/dress-blueprint-action)
- [Side-by-Side Blueprint](https://github.com/e-vergo/Side-By-Side-Blueprint)
