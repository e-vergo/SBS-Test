# SBS-Test

![Lean](https://img.shields.io/badge/Lean-v4.27.0-blue)
![License](https://img.shields.io/badge/License-Apache%202.0-green)

Minimal test project for the [Side-by-Side Blueprint](https://github.com/e-vergo/Side-By-Side-Blueprint) toolchain.

## Purpose

Fast iteration testing for toolchain development. Builds in ~2 minutes vs. 30+ minutes for production projects (GCR, PNT).

## Screenshots

![Dashboard](images/Dashboard.png)
*Dashboard homepage with stats and key theorems*

![Blueprint](images/blueprint.png)
*Side-by-side theorem display*

![Dependency Graph](images/dep_graph.png)
*Interactive dependency graph*

![Paper](images/paper_web.png)
*Paper web view*

## Features Tested

- **All 6 node status types**: notReady, ready, sorry, proven, fullyProven, mathlibReady
- **Graph validation**: Cycle detection (cycleA/cycleB), disconnected component detection
- **LaTeX references**: `\inputleannode{label}` and `\inputleanmodule{ModuleName}`
- **Paper generation**: `\paperstatement{}` and `\paperfull{}` hooks
- **Dashboard features**: keyDeclaration, message, priorityItem, blocked, potentialIssue, technicalDebt, misc

## Project Structure

```
SBS-Test/
├── SBSTest/
│   ├── StatusDemo.lean      # All 6 statuses + validation fixtures (cycles, disconnected)
│   └── ModuleRefTest.lean   # Module reference test
├── blueprint/src/
│   ├── blueprint.tex        # Main blueprint
│   └── paper.tex            # Paper generation test
└── runway.json              # Site configuration
```

## Building

The project uses GitHub Actions for CI/CD. See [dress-blueprint-action](https://github.com/e-vergo/dress-blueprint-action) for details.

To build locally, ensure you have the toolchain dependencies and run:

```bash
lake build
```

## Output

| Path | Contents |
|------|----------|
| `.lake/build/runway/index.html` | Dashboard homepage |
| `.lake/build/runway/dep_graph.html` | Dependency graph |
| `.lake/build/runway/manifest.json` | Precomputed stats + validation |
| `.lake/build/runway/paper.pdf` | Generated paper |

## Toolchain Repos

| Repo | Purpose |
|------|---------|
| [Runway](https://github.com/e-vergo/Runway) | Site generator |
| [Dress](https://github.com/e-vergo/Dress) | Artifact generation |
| [LeanArchitect](https://github.com/e-vergo/LeanArchitect) | `@[blueprint]` attribute |
| [subverso](https://github.com/e-vergo/subverso) | Syntax highlighting |
| [dress-blueprint-action](https://github.com/e-vergo/dress-blueprint-action) | CI/CD action + assets |

## Example Projects

| Repo | Scale |
|------|-------|
| [General_Crystallographic_Restriction](https://github.com/e-vergo/General_Crystallographic_Restriction) | Production example with paper |
| [PrimeNumberTheoremAnd](https://github.com/e-vergo/PrimeNumberTheoremAnd) | Large-scale (530 annotations) |

## Live Site

[e-vergo.github.io/SBS-Test](https://e-vergo.github.io/SBS-Test/)
