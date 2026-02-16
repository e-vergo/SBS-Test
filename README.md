# SBS-Test

![Lean](https://img.shields.io/badge/Lean-v4.27.0-blue)
![License](https://img.shields.io/badge/License-Apache%202.0-green)

Minimal test project for the [Side-by-Side Blueprint](https://github.com/e-vergo/SLS-Strange-Loop-Station) toolchain. Fast iteration environment for toolchain development, feature demonstration, and visual compliance testing.

**Live site:** [e-vergo.github.io/SBS-Test](https://e-vergo.github.io/SBS-Test/)

## Table of Contents

- [Purpose](#purpose)
- [Role in Pipeline](#role-in-pipeline)
- [Motivation](#motivation-the-tao-incident)
- [Features Tested](#features-tested)
- [Node Inventory](#node-inventory-33-total)
- [Project Structure](#project-structure)
- [Key Files](#key-files)
- [Building](#building)
- [Output Locations](#output-locations)
- [Configuration](#configuration)
- [Integration Points](#integration-points)
- [Validation Features](#validation-features)
- [Visual Compliance Testing](#visual-compliance-testing)
- [Status Color Model](#status-color-model)
- [Attribute Options Reference](#attribute-options-reference)
- [Using as a Template](#using-as-a-template)
- [Tooling & Archive System](#tooling--archive-system)
- [Related](#related)

## Purpose

SBS-Test is the primary test project for the Side-by-Side Blueprint toolchain. It exists to make development fast and reliable by providing:

1. **Fast iteration** - ~2 minute builds vs. 5-20 minutes for production projects
2. **Complete feature coverage** - All 7 status colors, 8 metadata options, 2 manual flags
3. **Validation testing** - Intentional graph errors (cycles, disconnected components)
4. **Security testing** - XSS prevention across all user-controlled fields
5. **Visual regression baseline** - Reference screenshots for automated compliance validation
6. **Template for new projects** - Demonstrates required structure and configuration

The project contains 33 `@[blueprint]` annotated nodes across 4 Lean files plus 1 pure LaTeX node.

## Role in Pipeline

SBS-Test serves as the fast iteration target during toolchain development:

| Project | Nodes | Build Time | Use Case |
|---------|-------|------------|----------|
| **SBS-Test** | 33 | ~2 min | Daily development, feature testing |
| GCR | 57 | ~5 min | Production validation with paper |
| PNT | 591 | ~20 min | Large-scale stress testing |

**When to use SBS-Test:**
- Testing changes to SubVerso, LeanArchitect, Dress, Runway, or Verso
- Developing new CSS/JS features in dress-blueprint-action
- Validating CI/CD workflow changes
- Creating visual regression baselines
- Debugging build pipeline issues

## Motivation: The Tao Incident

This project supports the Side-by-Side Blueprint toolchain, which was motivated by a January 2026 incident on Terence Tao's Prime Number Theorem project:

> "When reviewing the blueprint graph I noticed an oddity in the Erdos 392 project: the final theorems were mysteriously disconnected from the rest of the lemmas; and the (AI-provided) proofs were suspiciously short. After some inspection I realized the problem: I had asked to prove statements that n! can be factored into **at least** n factors... when in fact the Erdos problem asks for **at most** n factors."
>
> -- Terence Tao, PNT+ Zulip

SBS-Test specifically exercises the validation checks (connectivity, cycles) that would have caught this error automatically. The disconnected cycle (`cycle_a`, `cycle_b`) demonstrates exactly this failure mode.

## Features Tested

| Category | Coverage |
|----------|----------|
| Status colors | All 7: notReady, wip, sorry, proven, fullyProven, axiom, mathlibReady |
| Metadata options | All 8: title, keyDeclaration, message, priorityItem, blocked, potentialIssue, technicalDebt, misc |
| Manual status flags | Both: wip, mathlibReady |
| Graph validation | Disconnected component detection, cycle detection |
| Rainbow brackets | Nesting depths 1-10, all bracket types, color wrap-around |
| Module references | `\inputleanmodule{ModuleName}` expansion |
| Security | XSS prevention in all user-controlled fields |
| Output formats | Dashboard, side-by-side pages, dependency graph, paper (HTML + PDF) |
| Verso documents | SBSBlueprint genre with hook directives |

## Node Inventory (33 Total)

### StatusDemo.lean (14 nodes)

Demonstrates all 7 status colors and graph validation:

| Label | Status | Source | Purpose |
|-------|--------|--------|---------|
| `foundation` | notReady | Manual flag | Tests `(notReady := true)` override |
| `ready_to_prove` | wip | Manual flag | Tests `(wip := true)` |
| `another_ready` | wip | Manual flag | Second wip node |
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
├── images/                   # Screenshots for documentation
│   ├── Dashboard.png
│   ├── blueprint.png
│   ├── dep_graph.png
│   └── paper_web.png
└── .github/
    └── workflows/
        └── full-blueprint-build-and-deploy.yml
```

## Key Files

| File | Purpose |
|------|---------|
| `SBSTest.lean` | Library root - imports all modules for Lake build |
| `SBSTest/StatusDemo.lean` | Primary test file: 14 nodes covering all 7 statuses, graph validation |
| `SBSTest/BracketDemo.lean` | Rainbow bracket stress testing: depths 1-10, all bracket types |
| `SBSTest/SecurityTest.lean` | XSS prevention: script tags, event handlers, javascript URLs |
| `runway/src/blueprint.tex` | LaTeX blueprint structure with `\inputleannode{}` and `\inputleanmodule{}` |
| `runway/src/paper.tex` | Paper with `\paperstatement{}` and `\paperfull{}` hooks |
| `runway.json` | Runway configuration: title, projectName, assets path |
| `lakefile.toml` | Lake build configuration with Dress, Verso, mathlib dependencies |
| `GenerateBlueprint.lean` | Verso SBSBlueprint genre document generator |
| `GeneratePaper.lean` | Verso VersoPaper genre document generator |

## Building

### Local Development

From the Side-by-Side-Blueprint monorepo:

```bash
cd /path/to/Side-By-Side-Blueprint/toolchain/SBS-Test
python ../../dev/scripts/build.py
```

Alternatively, use the convenience script from the monorepo root:

```bash
cd /path/to/Side-By-Side-Blueprint
bash dev/build-sbs-test.sh
```

**Expected build time:** ~2 minutes (vs. ~5 minutes for GCR, ~20 minutes for PNT)

### Build Script Steps

The `build.py` script executes:

1. Validate project (check runway.json, extract projectName)
2. Kill existing servers on port 8000
3. Sync repos to GitHub (commits and pushes all changes)
4. Update lake manifests in dependency order
5. Clean all build artifacts
6. Build toolchain (SubVerso -> LeanArchitect -> Dress -> Runway)
7. Fetch mathlib cache
8. Build project with `BLUEPRINT_DRESS=1`
9. Build `:blueprint` facet
10. Generate dependency graph and manifest
11. Generate site with Runway
12. Generate paper (HTML + PDF)
13. Archive screenshots and metrics
14. Start server at http://localhost:8000

**Note:** The build script automatically commits and pushes all repository changes. There is no option to skip this—it ensures reproducible builds tied to specific commits.

### Manual Build Steps

If you need to run individual steps:

```bash
# Fetch mathlib cache
lake exe cache get

# Build with artifact generation
BLUEPRINT_DRESS=1 lake build

# Generate Lake facets
lake build :blueprint

# Generate dependency graph and manifest
lake exe extract_blueprint graph SBSTest

# Generate site
lake exe runway build runway.json
```

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
```

Trigger manually via GitHub Actions UI.

## Output Locations

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
├── library/
│   └── SBSTest.tex               # Aggregated LaTeX definitions
├── dep-graph.json                # Serialized graph structure
├── dep-graph.svg                 # Rendered SVG with Sugiyama layout
└── manifest.json                 # Precomputed stats and validation results
```

### Site Output

Located in `.lake/build/runway/`:

| File | Content |
|------|---------|
| `index.html` | Dashboard: stats, key theorems, messages, project notes |
| `dep_graph.html` | Interactive dependency graph with pan/zoom and modals |
| `manifest.json` | Copied from Dress; precomputed stats, validation results, metadata |
| `paper_tex.html` | Paper with MathJax rendering |
| `paper.pdf` | PDF output (if LaTeX compiler available) |
| `assets/` | CSS, JavaScript (copied from `assetsDir` in runway.json) |

### Archive & Metrics

**Screenshots:** Located in `../../dev/storage/SBSTest/` (relative to project root)

```
dev/storage/
├── SBSTest/
│   ├── latest/                   # Current capture (overwritten each build)
│   │   ├── capture.json          # Metadata: timestamp, commit, viewport, page status
│   │   ├── dashboard.png
│   │   ├── dep_graph.png
│   │   ├── blueprint.png
│   │   └── *_interactive.png
│   └── archive/                  # Timestamped history
│       └── {timestamp}/
├── unified_ledger.json           # Build metrics and timing (single source of truth)
├── compliance_ledger.json        # Compliance tracking per page
└── README.md                     # Central tooling hub documentation
```

**Refer to:** [`dev/storage/README.md`](../../dev/storage/README.md) for comprehensive CLI documentation (capture, compliance, archive, rubrics).

### What to Inspect

When verifying changes to the toolchain:

1. **Dashboard** (`index.html`)
   - Stats panel shows correct counts for all 7 statuses
   - Key Theorems panel lists nodes with `keyDeclaration := true`
   - Messages panel shows nodes with `message` field
   - Project Notes shows blocked/issues/debt/misc items

2. **Dependency Graph** (`dep_graph.html`)
   - Main component shows 31 connected nodes
   - Disconnected cycle (cycle_a, cycle_b) is separate
   - All 7 status colors appear correctly
   - Pan/zoom and modals function properly
   - Edge styles: solid (proof deps), dashed (statement deps)

3. **Chapter Pages**
   - Side-by-side LaTeX/Lean displays
   - Rainbow brackets with correct color cycling
   - Proof toggles expand/collapse in sync
   - Status dots in headers

4. **Manifest** (`manifest.json`)
   - `checkResults.connected`: false (due to disconnected cycle)
   - `checkResults.cycles`: contains `["cycle_a", "cycle_b"]`
   - `checkResults.componentCount`: 2
   - Stats match actual node counts

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

## Integration Points

SBS-Test integrates with every component in the toolchain:

### Upstream Dependencies

| Component | Integration |
|-----------|-------------|
| **SubVerso** | Syntax highlighting via `BLUEPRINT_DRESS=1` during elaboration |
| **LeanArchitect** | `@[blueprint]` attribute with all 8 metadata + 2 manual status options |
| **Dress** | Artifact generation, graph layout, validation checks |
| **Runway** | Site generation, dashboard, paper/PDF output |
| **Verso** | SBSBlueprint and VersoPaper genres via `GenerateBlueprint.lean` |
| **dress-blueprint-action** | CSS/JS assets via `assetsDir` config |

### Data Flow

```
@[blueprint "label"] theorem ...
        |
        v
LeanArchitect: Stores Node in environment extension
        |
        v
Dress (BLUEPRINT_DRESS=1): Captures highlighting, writes artifacts
        |
        v
Lake facets: Aggregates into manifest.json
        |
        v
Runway: Generates .lake/build/runway/ site
```

### Testing Points

SBS-Test validates:
- **Dress artifacts**: Check `.lake/build/dressed/SBSTest/` for per-declaration output
- **Manifest generation**: Verify `manifest.json` stats and checkResults
- **Site output**: Inspect `.lake/build/runway/` pages
- **Graph layout**: SVG in `dep_graph.html` with correct node positions
- **Status computation**: `fullyProven` propagation through dependency chains

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

This is the exact failure mode from the Tao incident: a "proven" theorem that wasn't actually connected to the foundational lemmas it claimed to use.

### Cycle Detection

`cycle_a` and `cycle_b` form a mutual dependency:

```json
{
  "cycles": [["cycle_a", "cycle_b"]]
}
```

Cycles indicate logical errors in the dependency structure that need to be resolved.

## Visual Compliance Testing

SBS-Test serves as the reference project for the visual compliance validation system:

### Screenshot Capture

```bash
cd /path/to/Side-By-Side-Blueprint/dev/scripts

# Capture screenshots after a build
python3 -m sbs capture --project SBSTest --interactive
```

Captures 8 pages plus interactive states (theme toggles, zoom controls, node clicks, proof toggles).

### Compliance Validation

```bash
# Run compliance validation
python3 -m sbs compliance --project SBSTest
```

The compliance system:
- Uses AI vision analysis to validate screenshots against expected criteria
- Tracks pass/fail status per page in a persistent ledger
- Detects repo changes and revalidates affected pages
- Loops until 100% compliance achieved

**See:** [`dev/scripts/VISUAL_COMPLIANCE.md`](../../dev/scripts/VISUAL_COMPLIANCE.md) for comprehensive documentation on the compliance system.

### Screenshot Storage

Screenshots are stored in the centralized archive system at `dev/storage/`:

```
dev/storage/
  SBSTest/
    latest/           # Current capture (overwritten each build)
      capture.json    # Metadata: timestamp, commit, viewport, page status
      dashboard.png
      dep_graph.png
      paper_tex.png
      blueprint.png
      *_interactive.png
    archive/          # Timestamped history
      {timestamp}/
```

Metadata about all captures is tracked in:
- `dev/storage/compliance_ledger.json` - Pass/fail status per page
- `dev/storage/unified_ledger.json` - Build metrics and timing
- `dev/storage/COMPLIANCE_STATUS.md` - Human-readable status report

### Standard Visual Verification Workflow

1. **Build:** `python ../../dev/scripts/build.py` (auto-archives old screenshots, captures new ones)
2. **Make changes** to CSS/JS/Lean/templates
3. **Rebuild:** `python ../../dev/scripts/build.py` (auto-captures for comparison)
4. **Verify:** `python3 -m sbs compare` (view differences between old and new captures)
5. **Validate:** `python3 -m sbs compliance --project SBSTest` (AI vision analysis)

The build script automatically handles screenshot management—no manual capture steps needed.

## Status Color Model

| Status | Color | Hex | Source |
|--------|-------|-----|--------|
| notReady | Vivid Orange | #E8820C | Default -- no Lean proof exists |
| wip | Deep Teal | #0097A7 | `(wip := true)` |
| sorry | Vivid Red | #C62828 | Auto-detected from proof |
| proven | Medium Green | #66BB6A | Auto-detected (complete proof) |
| fullyProven | Deep Forest Green | #1B5E20 | Auto-computed (all ancestors proven) |
| axiom | Vivid Purple | #7E57C2 | Auto-detected (Lean `axiom` declaration) |
| mathlibReady | Vivid Blue | #42A5F5 | `(mathlibReady := true)` |

**Priority order** (highest to lowest): mathlibReady > wip > notReady (manual) > fullyProven > axiom > sorry > proven > notReady (default)

The `fullyProven` status is computed via O(V+E) graph traversal with memoization: a node is fullyProven if it is proven and all its ancestors are proven or fullyProven.

## Attribute Options Reference

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

### Manual Status Flags (2)

| Option | Effect |
|--------|--------|
| `(wip := true)` | Deep Teal (#0097A7) |
| `(mathlibReady := true)` | Vivid Blue (#42A5F5) |

### Dependency Options

| Option | Effect |
|--------|--------|
| `(uses := ["label1", "label2"])` | Explicit statement dependencies |
| `(statement := /-- LaTeX with \uses{...} -/)` | Statement content |
| `(proof := /-- Proof explanation -/)` | Proof content |

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
   lake exe cache get  # if using mathlib
   BLUEPRINT_DRESS=1 lake build
   lake build :blueprint
   lake exe extract_blueprint graph MyProject
   lake exe runway build runway.json
   # Open .lake/build/runway/index.html
   ```

## Tooling & Archive System

For comprehensive CLI documentation, see the **[Storage & Tooling Hub](../../dev/storage/README.md)** (centralized reference).

This hub documents:
- `sbs capture` / `sbs compliance` - Visual testing workflows
- `sbs rubric` - Custom quality rubrics
- `sbs archive` - Build history, metrics, iCloud sync
- Validator infrastructure and quality scoring (T1-T8 test suite)

### Quick Reference for SBS-Test Development

```bash
cd /path/to/Side-By-Side-Blueprint/dev/scripts

# Capture screenshots after build
python3 -m sbs capture --project SBSTest --interactive

# Run visual compliance validation
python3 -m sbs compliance --project SBSTest

# List build history for this project
python3 -m sbs archive list --project SBSTest

# Generate trend charts
python3 -m sbs archive charts
```

### Common Commands

| Command | Purpose |
|---------|---------|
| `sbs capture --project SBSTest` | Screenshot all pages (static) |
| `sbs capture --project SBSTest --interactive` | Include hover/click states |
| `sbs compliance --project SBSTest` | AI vision validation against criteria |
| `sbs compare` | View differences between captures |
| `sbs archive list --project SBSTest` | List build history |
| `sbs archive charts` | Generate timing/LOC trend visualizations |

### Build & Archive Integration

The `build.py` script automatically:
- Captures screenshots after successful builds (via `sbs capture --interactive`)
- Archives previous screenshots with timestamps
- Updates `dev/storage/unified_ledger.json` with build metrics
- Updates `dev/storage/compliance_ledger.json` with page status
- Syncs to iCloud (if configured)

## Related

### Toolchain

```
SubVerso -> LeanArchitect -> Dress -> Runway
              |
              +-> Verso (genres)
```

| Component | Purpose |
|-----------|---------|
| [SubVerso](../../forks/subverso/) | Syntax highlighting with O(1) indexed lookups |
| [LeanArchitect](../../forks/LeanArchitect/) | `@[blueprint]` attribute definition |
| [Dress](../Dress/) | Artifact generation, graph layout, validation |
| [Verso](../../forks/verso/) | Document genres (SBSBlueprint, VersoPaper) |
| [Runway](../Runway/) | Site generator |
| [dress-blueprint-action](../dress-blueprint-action/) | CI/CD action + CSS/JS assets |

### Projects

| Project | Description |
|---------|-------------|
| [Side-By-Side-Blueprint](../..) | Parent monorepo with full toolchain |
| [General_Crystallographic_Restriction](../../showcase/General_Crystallographic_Restriction/) | Production example with paper (57 nodes) |
| [PrimeNumberTheoremAnd](../../showcase/PrimeNumberTheoremAnd/) | Large-scale integration (591 annotations) |

## License

Apache 2.0
