# SBS-Test

Minimal test project for the [Side-by-Side Blueprint](https://github.com/e-vergo/Side-By-Side-Blueprint) toolchain.

SBS-Test provides a controlled environment for testing all features of the blueprint system with fast iteration times (~2 minutes vs. 30+ minutes for production projects). It contains 32 `@[blueprint]` annotated declarations across 4 Lean files, plus 1 pure LaTeX node, exercising the full feature set.

**Live site:** [e-vergo.github.io/SBS-Test](https://e-vergo.github.io/SBS-Test/)

## Features Tested

| Category | Coverage |
|----------|----------|
| Status colors | All 6: notReady, ready, sorry, proven, fullyProven, mathlibReady |
| Metadata options | All 8: title, keyDeclaration, message, priorityItem, blocked, potentialIssue, technicalDebt, misc |
| Manual status flags | All 3: notReady, ready, mathlibReady |
| Graph validation | Cycle detection, disconnected component detection |
| Rainbow brackets | Nesting depths 1-10, all bracket types, color wrap-around |
| Module references | `\inputleanmodule{ModuleName}` expansion |
| Security | XSS prevention in all user-controlled fields |
| Output formats | Dashboard, side-by-side pages, dependency graph, paper (HTML + PDF) |

## Dependencies

The toolchain dependency chain:

```
SubVerso -> LeanArchitect -> Dress -> Runway
              |
              +-> Verso (genres)
```

| Repository | Purpose |
|------------|---------|
| [SubVerso](https://github.com/e-vergo/subverso) | Syntax highlighting extraction with O(1) indexed lookups |
| [LeanArchitect](https://github.com/e-vergo/LeanArchitect) | `@[blueprint]` attribute definition |
| [Dress](https://github.com/e-vergo/Dress) | Artifact generation, graph layout, validation |
| [Verso](https://github.com/e-vergo/verso) | Document genres (SBSBlueprint, VersoPaper) |
| [Runway](https://github.com/e-vergo/Runway) | Site generator |
| [dress-blueprint-action](https://github.com/e-vergo/dress-blueprint-action) | CI/CD action + CSS/JS assets |

## Node Inventory (33 Total)

### StatusDemo.lean (14 nodes)

Demonstrates all 6 status colors and graph validation:

| Label | Status | Source | Purpose |
|-------|--------|--------|---------|
| `foundation` | notReady | Manual flag | Tests `(notReady := true)` override |
| `ready_to_prove` | ready | Manual flag | Tests `(ready := true)` |
| `another_ready` | ready | Manual flag | Second ready node |
| `has_sorry` | sorry | Auto-detected | Contains `sorry` in proof |
| `also_sorry` | sorry | Auto-detected | Second sorry node |
| `proven_leaf` | fullyProven | Auto-computed | Complete proof, no dependencies |
| `proven_mid` | proven | Auto-detected | Complete proof, has sorry dependency |
| `proven_chain` | proven | Auto-detected | Continues dependency chain |
| `fully_chain_1` | fullyProven | Auto-computed | First in verified chain |
| `fully_chain_2` | fullyProven | Auto-computed | Second in verified chain |
| `fully_chain_3` | fullyProven | Auto-computed | Third in verified chain |
| `mathlib_theorem` | mathlibReady | Manual flag | Tests `(mathlibReady := true)` |
| `cycle_a` | proven | Auto-detected | Part of disconnected cycle |
| `cycle_b` | proven | Auto-detected | Part of disconnected cycle |

**Graph structure:** Main component has 12 connected nodes plus `base_axiom` (pure LaTeX). Two nodes (`cycle_a`, `cycle_b`) form a disconnected cycle for validation testing.

### BracketDemo.lean (8 nodes)

Tests rainbow bracket highlighting:

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

Tests `\inputleanmodule{ModuleName}` feature:

| Label | Description |
|-------|-------------|
| `mod:first` | First declaration in module |
| `mod:second` | Second declaration, depends on first |

### SecurityTest.lean (8 nodes)

Tests XSS prevention in user-controlled fields:

| Label | Attack Vector |
|-------|---------------|
| `xss_title` | Script tag in title field |
| `xss_message` | Img onerror handler in message |
| `xss_blocked` | SVG onload handler in blocked |
| `xss_issue` | Iframe javascript: URL in potentialIssue |
| `xss_debt` | Event handler in technicalDebt |
| `xss_misc` | Javascript URL in misc |
| `xss_label` | Mixed escaped/unescaped HTML |
| `xss_quotes` | Quote injection in attributes |

### blueprint.tex (1 pure LaTeX node)

| Label | Description |
|-------|-------------|
| `base_axiom` | Pure LaTeX axiom with no Lean code (notReady status) |

## Attribute Options Demonstrated

### Metadata Options (8)

| Option | Example |
|--------|---------|
| `title` | `(title := "Foundation")` |
| `keyDeclaration` | `(keyDeclaration := true)` |
| `message` | `(message := "Ready for formalization")` |
| `priorityItem` | `(priorityItem := true)` |
| `blocked` | `(blocked := "Waiting for upstream lemma")` |
| `potentialIssue` | `(potentialIssue := "Edge case not handled")` |
| `technicalDebt` | `(technicalDebt := "Needs refactoring")` |
| `misc` | `(misc := "PR #12345 submitted")` |

### Manual Status Flags (3)

| Option | Effect |
|--------|--------|
| `(notReady := true)` | Sandy brown (#F4A460) |
| `(ready := true)` | Light sea green (#20B2AA) |
| `(mathlibReady := true)` | Light blue (#87CEEB) |

### Dependency Options

| Option | Effect |
|--------|--------|
| `(uses := ["label1", "label2"])` | Explicit statement dependencies |
| `(statement := /-- LaTeX with \uses{...} -/)` | Statement content |
| `(proof := /-- Proof explanation -/)` | Proof content |

## Project Structure

```
SBS-Test/
├── SBSTest.lean              # Library root (imports all modules)
├── SBSTest/
│   ├── StatusDemo.lean       # 14 nodes: status colors, validation
│   ├── BracketDemo.lean      # 8 nodes: rainbow bracket testing
│   ├── ModuleRefTest.lean    # 2 nodes: module reference testing
│   ├── SecurityTest.lean     # 8 nodes: XSS prevention testing
│   ├── Blueprint.lean        # Verso SBSBlueprint document
│   └── Paper.lean            # Verso paper document
├── runway/
│   └── src/
│       ├── blueprint.tex     # Main LaTeX blueprint
│       └── paper.tex         # Paper with status badges
├── GenerateBlueprint.lean    # Verso blueprint generator executable
├── GeneratePaper.lean        # Verso paper generator executable
├── runway.json               # Site configuration
├── lakefile.toml             # Lake build configuration
├── scripts/
│   └── build_blueprint.sh    # Build script wrapper
└── images/                   # Screenshots for README
```

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
| `projectName` | Must match the Lean library name in lakefile.toml |
| `runwayDir` | Directory containing `src/blueprint.tex` and `src/paper.tex` |
| `assetsDir` | Path to CSS/JS assets from dress-blueprint-action |

### lakefile.toml

```toml
name = "SBSTest"
defaultTargets = ["SBSTest"]

[leanOptions]
pp.unicode.fun = true
autoImplicit = false
relaxedAutoImplicit = false

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

[[lean_lib]]
name = "SBSTest"

[[lean_exe]]
name = "generate-blueprint-verso"
root = "GenerateBlueprint"

[[lean_exe]]
name = "generate-paper-verso"
root = "GeneratePaper"
```

## Building

### Local Development

```bash
cd /path/to/SBS-Test
./scripts/build_blueprint.sh
```

The build script executes:

1. Validate project (check runway.json, extract projectName)
2. Kill existing servers on port 8000
3. Sync repos to GitHub
4. Update lake manifests in dependency order
5. Clean all build artifacts
6. Build toolchain (SubVerso -> LeanArchitect -> Dress -> Runway)
7. Fetch mathlib cache
8. Build project with `BLUEPRINT_DRESS=1`
9. Build `:blueprint` facet
10. Generate dependency graph
11. Generate site with Runway
12. Generate paper (HTML + PDF)
13. Start server at http://localhost:8000

### CI/CD

GitHub Actions workflow (`.github/workflows/full-blueprint-build-and-deploy.yml`):

```yaml
name: Full Blueprint Build and Deploy

on:
  workflow_dispatch:

permissions:
  contents: read
  pages: write
  id-token: write

jobs:
  build:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: e-vergo/dress-blueprint-action@main

  deploy:
    needs: build
    if: github.ref == 'refs/heads/main'
    runs-on: ubuntu-latest
    environment:
      name: github-pages
      url: ${{ steps.deployment.outputs.page_url }}
    steps:
      - uses: actions/deploy-pages@v4
        id: deployment
```

Trigger manually via GitHub Actions UI.

## Output Artifacts

### Dressed Artifacts

Located in `.lake/build/dressed/`:

```
.lake/build/dressed/
├── SBSTest/
│   ├── StatusDemo/
│   │   ├── foundation/
│   │   │   ├── decl.tex          # LaTeX source
│   │   │   ├── decl.html         # Syntax-highlighted HTML
│   │   │   ├── decl.json         # Metadata
│   │   │   └── decl.hovers.json  # Hover tooltip data
│   │   └── ...
│   ├── BracketDemo/
│   ├── ModuleRefTest/
│   └── SecurityTest/
└── library/
    └── SBSTest.tex               # Aggregated LaTeX definitions
```

### Site Output

Located in `.lake/build/runway/`:

| File | Content |
|------|---------|
| `index.html` | Dashboard: stats, key theorems, messages, project notes |
| `dep_graph.html` | Interactive dependency graph with pan/zoom and modals |
| `manifest.json` | Precomputed stats, validation results, metadata |
| `paper.html` | Paper with MathJax rendering |
| `paper.pdf` | PDF output (if LaTeX compiler available) |
| `assets/` | CSS, JavaScript |

## Validation Features

SBS-Test exercises graph validation checks that detect common blueprint errors:

### Disconnected Component Detection

The `cycle_a` and `cycle_b` nodes are not connected to the main graph. The validator reports:

```json
{
  "connected": false,
  "componentCount": 2,
  "componentSizes": [31, 2]
}
```

### Cycle Detection

`cycle_a` and `cycle_b` form a mutual dependency:

```json
{
  "cycles": [["cycle_a", "cycle_b"]]
}
```

These checks help catch logical errors in blueprint structure (e.g., the Tao incident where a disconnected lemma was not used in the main proof).

## Status Color Model

| Status | Color | Hex | Source |
|--------|-------|-----|--------|
| notReady | Sandy Brown | #F4A460 | Default or `(notReady := true)` |
| ready | Light Sea Green | #20B2AA | `(ready := true)` |
| sorry | Dark Red | #8B0000 | Auto-detected from proof |
| proven | Light Green | #90EE90 | Auto-detected (complete proof) |
| fullyProven | Forest Green | #228B22 | Auto-computed (all ancestors proven) |
| mathlibReady | Light Blue | #87CEEB | `(mathlibReady := true)` |

**Priority order** (highest to lowest): mathlibReady > fullyProven > sorry > proven > ready > notReady

The `fullyProven` status is computed via graph traversal: a node is fullyProven if it is proven and all its ancestors are proven or fullyProven.

## Screenshots

![Dashboard](images/Dashboard.png)
*Dashboard homepage: 2x2 grid with Stats, Key Theorems, Messages, Project Notes*

![Blueprint](images/blueprint.png)
*Side-by-side theorem display with proof toggle*

![Dependency Graph](images/dep_graph.png)
*Interactive dependency graph with Sugiyama layout*

![Paper](images/paper_web.png)
*Paper output with status badges*

## Using as a Template

To create a new blueprint project based on SBS-Test:

1. **Clone and rename:**
   ```bash
   git clone https://github.com/e-vergo/SBS-Test MyProject
   cd MyProject
   rm -rf .git && git init
   ```

2. **Update configuration:**
   - `lakefile.toml`: Change `name = "SBSTest"` to your project name
   - `runway.json`: Update `title`, `projectName`, `githubUrl`, `baseUrl`
   - Rename `SBSTest/` directory and `SBSTest.lean` to match your project name

3. **Replace demo content:**
   - Delete contents of your renamed module directory
   - Create your own `@[blueprint]` annotated declarations
   - Update `runway/src/blueprint.tex` with your LaTeX structure
   - Optionally update `runway/src/paper.tex` for paper output

4. **Update imports:**
   - Edit your library root file to import your modules
   - Update `GenerateBlueprint.lean` and `GeneratePaper.lean` imports

5. **Build and verify:**
   ```bash
   ./scripts/build_blueprint.sh
   # Open http://localhost:8000
   ```

## Related Projects

### Toolchain

| Repository | Purpose |
|------------|---------|
| [SubVerso](https://github.com/e-vergo/subverso) | Syntax highlighting extraction |
| [LeanArchitect](https://github.com/e-vergo/LeanArchitect) | `@[blueprint]` attribute |
| [Dress](https://github.com/e-vergo/Dress) | Artifact generation and graph layout |
| [Verso](https://github.com/e-vergo/verso) | Document framework |
| [Runway](https://github.com/e-vergo/Runway) | Site generator |
| [dress-blueprint-action](https://github.com/e-vergo/dress-blueprint-action) | CI/CD action + assets |

### Production Projects

| Repository | Scale |
|------------|-------|
| [General_Crystallographic_Restriction](https://github.com/e-vergo/General_Crystallographic_Restriction) | Production example with paper (57 nodes) |
| [PrimeNumberTheoremAnd](https://github.com/e-vergo/PrimeNumberTheoremAnd) | Large-scale integration (530 nodes) |

## License

Apache 2.0
