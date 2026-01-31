# SBS-Test

Minimal test project for the [Side-by-Side Blueprint](https://github.com/e-vergo/Side-By-Side-Blueprint) toolchain.

SBS-Test provides a controlled environment for testing all features of the blueprint system with fast iteration times (~2 minutes vs. 30+ minutes for production projects). It contains 24 `@[blueprint]` annotated declarations across 3 Lean files, plus 1 pure LaTeX node, that exercise every aspect of the toolchain.

## Dependencies

This project depends on the following toolchain components:

- [SubVerso](https://github.com/e-vergo/subverso) - Syntax highlighting extraction with O(1) indexed lookups
- [LeanArchitect](https://github.com/e-vergo/LeanArchitect) - `@[blueprint]` attribute for marking declarations
- [Dress](https://github.com/e-vergo/Dress) - Artifact generation, graph layout, and validation
- [Verso](https://github.com/e-vergo/verso) - Document genres for blueprint and paper rendering
- [Runway](https://github.com/e-vergo/Runway) - Site generator

The dependency chain is: `SubVerso -> LeanArchitect -> Dress -> Runway`

## Node Inventory (25 Total: 24 Lean + 1 LaTeX)

### StatusDemo.lean (14 nodes)

Demonstrates all 6 status colors and validation features:

| Label | Status | Source | Description |
|-------|--------|--------|-------------|
| `foundation` | notReady | Manual `(notReady := true)` | Foundation lemma with manual flag override (uses base_axiom) |
| `ready_to_prove` | ready | Manual `(ready := true)` | Theorem ready for formalization |
| `another_ready` | ready | Manual `(ready := true)` | Second ready theorem |
| `has_sorry` | sorry | Auto-detected | Theorem with `sorry` in proof |
| `also_sorry` | sorry | Auto-detected | Second sorry theorem |
| `proven_leaf` | proven | Auto-detected | Complete proof, no dependencies |
| `proven_mid` | proven | Auto-detected | Complete proof, has sorry dependency |
| `proven_chain` | proven | Auto-detected | Complete proof continuing chain |
| `fully_chain_1` | fullyProven | Auto-computed | Proven with all proven ancestors |
| `fully_chain_2` | fullyProven | Auto-computed | Second in fully proven chain |
| `fully_chain_3` | fullyProven | Auto-computed | Third in fully proven chain |
| `mathlib_theorem` | mathlibReady | Manual `(mathlibReady := true)` | Ready for mathlib submission |
| `cycle_a` | proven | Auto-detected | Part of disconnected cycle |
| `cycle_b` | proven | Auto-detected | Part of disconnected cycle |

**Graph structure**: The main component has 12 connected nodes plus `base_axiom` (a pure LaTeX node with no Lean code), and 2 disconnected nodes forming a cycle (cycle_a, cycle_b). The cycle tests both cycle detection and disconnected component detection.

### BracketDemo.lean (8 nodes)

Tests rainbow bracket highlighting with various nesting patterns:

| Label | Description |
|-------|-------------|
| `bracket:nested` | 3 levels of nested parentheses |
| `bracket:function` | Mixed brackets in function definition |
| `bracket:types` | Implicit type parameters with curly braces |
| `bracket:deep` | 8 levels testing color wrap-around |
| `bracket:mixed_deep` | All bracket types at depth 7+ |
| `bracket:complex` | Realistic filtering function |
| `bracket:realistic` | Pattern matching with comments |
| `bracket:extreme` | 10 levels for stress testing |

### ModuleRefTest.lean (2 nodes)

Tests the `\inputleanmodule{ModuleName}` feature:

| Label | Description |
|-------|-------------|
| `mod:first` | First declaration in module |
| `mod:second` | Second declaration, depends on first |

### blueprint.tex (1 pure LaTeX node)

| Label | Description |
|-------|-------------|
| `base_axiom` | A pure LaTeX axiom with no Lean code (demonstrates notReady status for unformalized content) |

## Attribute Options Exercised

### Metadata Options (8)

| Option | Example Usage |
|--------|---------------|
| `title` | `(title := "Foundation")` - Custom graph label |
| `keyDeclaration` | `(keyDeclaration := true)` - Dashboard highlight |
| `message` | `(message := "Ready for formalization")` - User notes |
| `priorityItem` | `(priorityItem := true)` - Attention column |
| `blocked` | `(blocked := "Waiting for upstream lemma")` - Blockage reason |
| `potentialIssue` | `(potentialIssue := "Edge case not handled")` - Known concerns |
| `technicalDebt` | `(technicalDebt := "Needs refactoring")` - Cleanup notes |
| `misc` | `(misc := "PR #12345 submitted")` - Catch-all notes |

### Manual Status Flags (3)

| Option | Effect |
|--------|--------|
| `(notReady := true)` | Forces notReady status (sandy brown) |
| `(ready := true)` | Forces ready status (light sea green) |
| `(mathlibReady := true)` | Forces mathlibReady status (light blue) |

### Dependency Options

| Option | Effect |
|--------|--------|
| `(uses := ["label1", "label2"])` | Explicit statement dependencies |
| `(statement := /-- LaTeX text \uses{...} -/)` | Statement content with embedded uses |
| `(proof := /-- Proof explanation -/)` | Proof content |

## Verso Documents

### Blueprint.lean

A Verso document using the `SBSBlueprint` genre that demonstrates:

- `:::leanNode "label"` - Full side-by-side display
- `:::leanModule "SBSTest.StatusDemo"` - All nodes from a module
- Prose between declarations

```lean
#doc (SBSBlueprint) "SBS-Test Blueprint" =>

# The Fully Proven Chain

:::leanNode "proven_leaf"
:::

:::leanNode "fully_chain_1"
:::
```

### Paper.lean

A Verso document demonstrating paper-style output:

- `:::paperStatement "label"` - Statement with Lean signature link
- `:::paperFull "label"` - Full side-by-side display
- `:::paperProof "label"` - Proof body extraction

```lean
#doc (SBSBlueprint) "SBS-Test Paper" =>

:::paperStatement "proven_leaf"
:::

:::paperFull "fully_chain_1"
:::
```

## TeX Pipeline

### blueprint.tex

The main blueprint document at `runway/src/blueprint.tex`:

- Inputs dressed artifacts via `\input{../../.lake/build/dressed/library/SBSTest.tex}`
- Uses `\inputleannode{label}` for individual declarations
- Uses `\inputleanmodule{SBSTest.ModuleRefTest}` for module-level import
- Standard LaTeX theorem environments (theorem, lemma, definition, axiom)

### paper.tex

Paper generation document at `runway/src/paper.tex`:

- Uses `\paperfull{label}` for side-by-side display with status badge
- Demonstrates all 6 status types with colored indicator dots
- Generates both HTML (`paper.html`) and PDF (`paper.pdf`) output

## Configuration

### runway.json

```json
{
  "title": "SBS-Test: Blueprint Feature Demonstration",
  "projectName": "SBSTest",
  "githubUrl": "https://github.com/e-vergo/SBS-Test",
  "baseUrl": "/SBS-Test/",
  "docgen4Url": null,
  "runwayDir": "runway",
  "assetsDir": "../dress-blueprint-action/assets"
}
```

| Field | Purpose |
|-------|---------|
| `title` | Site title displayed in dashboard |
| `projectName` | Must match the Lean library name |
| `githubUrl` | Links to GitHub source |
| `baseUrl` | URL prefix for deployment |
| `runwayDir` | Directory containing `src/blueprint.tex` and `src/paper.tex` |
| `assetsDir` | Path to CSS/JS assets (from dress-blueprint-action) |

### lakefile.toml

```toml
name = "SBSTest"
defaultTargets = ["SBSTest"]

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "v4.27.0"

[[require]]
name = "Dress"
git = "https://github.com/e-vergo/Dress.git"
rev = "main"

[[require]]
name = "verso"
git = "https://github.com/e-vergo/verso.git"
rev = "main"
```

## Building

### Local Development

```bash
cd /Users/eric/GitHub/Side-By-Side-Blueprint/SBS-Test
./scripts/build_blueprint.sh
```

The build script (~245 lines, shared across projects) executes:

1. Validate project (check runway.json, extract projectName)
2. Kill existing servers on port 8000
3. Sync all repos to GitHub
4. Update lake manifests in dependency order
5. Clean all build artifacts (eliminates stale caches)
6. Build toolchain (SubVerso -> LeanArchitect -> Dress -> Runway)
7. Fetch mathlib cache (`lake exe cache get`)
8. Build project with `BLUEPRINT_DRESS=1`
9. Build `:blueprint` facet
10. Generate dependency graph
11. Generate site with Runway
12. Generate paper (if paperTexPath configured)
13. Start server at http://localhost:8000

### CI/CD

GitHub Actions workflow using [dress-blueprint-action](https://github.com/e-vergo/dress-blueprint-action):

```yaml
on:
  workflow_dispatch:

jobs:
  build:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: e-vergo/dress-blueprint-action@main
```

## Output Artifacts

### Dressed Artifacts

Located in `.lake/build/dressed/`:

```
.lake/build/dressed/
├── SBSTest/
│   ├── StatusDemo/
│   │   ├── foundation/
│   │   │   ├── decl.tex      # LaTeX source
│   │   │   ├── decl.html     # Syntax-highlighted HTML
│   │   │   ├── decl.json     # Metadata
│   │   │   └── decl.hovers.json  # Hover tooltip data
│   │   ├── ready_to_prove/
│   │   │   └── ...
│   │   └── ...
│   ├── BracketDemo/
│   │   └── ...
│   └── ModuleRefTest/
│       └── ...
└── library/
    └── SBSTest.tex           # Aggregated LaTeX definitions
```

### Site Output

Located in `.lake/build/runway/`:

| File | Content |
|------|---------|
| `index.html` | Dashboard homepage with stats, key theorems, messages, project notes |
| `dep_graph.html` | Interactive dependency graph with pan/zoom and modals |
| `manifest.json` | Precomputed stats, validation results, project metadata |
| `paper.html` | Paper with MathJax rendering |
| `paper.pdf` | PDF output (if LaTeX compiler available) |
| `pdf.html` | PDF viewer page |
| `assets/` | CSS, JavaScript, fonts |

### manifest.json Structure

```json
{
  "nodes": [...],
  "edges": [...],
  "stats": {
    "notReady": 1,
    "ready": 2,
    "sorry": 2,
    "proven": 4,
    "fullyProven": 3,
    "mathlibReady": 1,
    "total": 15
  },
  "checkResults": {
    "connected": false,
    "componentCount": 2,
    "componentSizes": [13, 2],
    "cycles": [["cycle_a", "cycle_b"]]
  },
  "keyDeclarations": ["fully_chain_1", "mathlib_theorem"],
  "messages": [...],
  "projectNotes": {
    "blocked": [...],
    "potentialIssues": [...],
    "technicalDebt": [...],
    "misc": [...]
  }
}
```

## Validation Features

SBS-Test exercises two graph validation checks:

### Disconnected Component Detection

The cycle_a and cycle_b nodes are not connected to the main graph (13 nodes). The validator reports:

- `connected: false`
- `componentCount: 2`
- `componentSizes: [13, 2]`

### Cycle Detection

cycle_a and cycle_b form a mutual dependency:

- cycle_a uses cycle_b
- cycle_b uses cycle_a

The validator reports: `cycles: [["cycle_a", "cycle_b"]]`

## Status Color Model

| Status | Color | Hex | Source |
|--------|-------|-----|--------|
| notReady | Sandy Brown | #F4A460 | Default or `(notReady := true)` |
| ready | Light Sea Green | #20B2AA | Manual `(ready := true)` |
| sorry | Dark Red | #8B0000 | Auto-detected from proof |
| proven | Light Green | #90EE90 | Auto-detected (complete proof) |
| fullyProven | Forest Green | #228B22 | Auto-computed (all ancestors proven) |
| mathlibReady | Light Blue | #87CEEB | Manual `(mathlibReady := true)` |

**Priority order** (highest to lowest): mathlibReady, fullyProven, sorry, proven, ready, notReady.

The `fullyProven` status is computed by graph traversal: a node is fullyProven if it is proven and all its ancestors are proven or fullyProven.

## Screenshots

![Dashboard](images/Dashboard.png)
*Dashboard homepage with 2x2 grid: Stats, Key Theorems, Messages, Project Notes*

![Blueprint](images/blueprint.png)
*Side-by-side theorem display with proof toggle*

![Dependency Graph](images/dep_graph.png)
*Interactive dependency graph with Sugiyama layout*

![Paper](images/paper_web.png)
*Paper output with status badges*

## Live Site

[e-vergo.github.io/SBS-Test](https://e-vergo.github.io/SBS-Test/)

## Related Projects

### Toolchain

| Repository | Purpose |
|------------|---------|
| [SubVerso](https://github.com/e-vergo/subverso) | Syntax highlighting extraction |
| [LeanArchitect](https://github.com/e-vergo/LeanArchitect) | `@[blueprint]` attribute |
| [Dress](https://github.com/e-vergo/Dress) | Artifact generation and graph layout |
| [Verso](https://github.com/e-vergo/verso) | Document framework with blueprint genres |
| [Runway](https://github.com/e-vergo/Runway) | Site generator |
| [dress-blueprint-action](https://github.com/e-vergo/dress-blueprint-action) | CI/CD action + assets |

### Production Projects

| Repository | Scale |
|------------|-------|
| [General_Crystallographic_Restriction](https://github.com/e-vergo/General_Crystallographic_Restriction) | Production example with paper |
| [PrimeNumberTheoremAnd](https://github.com/e-vergo/PrimeNumberTheoremAnd) | Large-scale (530 annotations, 33 files) |

## License

Apache 2.0
