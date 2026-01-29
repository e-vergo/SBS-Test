# SBS-Test

Minimal test project for the [Side-by-Side Blueprint](https://github.com/e-vergo/Side-By-Side-Blueprint) toolchain.

## Purpose

Fast iteration testing for toolchain development. Builds in ~2 minutes vs. 30+ minutes for production projects (GCR, PNT).

## Features Tested

- **All 8 node status types**: notReady, stated, ready, sorry, proven, fullyProven, mathlibReady, inMathlib
- **Graph validation**: Cycle detection (cycleA/cycleB), disconnected component detection
- **LaTeX references**: `\inputleannode{label}` and `\inputleanmodule{ModuleName}`
- **Paper generation**: `\paperstatement{}` and `\paperfull{}` hooks
- **Dashboard features**: keyDeclaration, message, priorityItem, blocked, potentialIssue, technicalDebt, misc

## Project Structure

```
SBS-Test/
├── SBSTest/
│   ├── StatusDemo.lean      # All 8 statuses + validation fixtures (cycles, disconnected)
│   └── ModuleRefTest.lean   # Module reference test
├── blueprint/src/
│   ├── blueprint.tex        # Main blueprint
│   └── paper.tex            # Paper generation test
├── runway.json              # Site configuration
└── scripts/build_blueprint.sh
```

## Building

```bash
cd /Users/eric/GitHub/Side-By-Side-Blueprint/SBS-Test
./scripts/build_blueprint.sh
# Opens localhost:8000 when complete
```

## Output

| Path | Contents |
|------|----------|
| `.lake/build/runway/index.html` | Dashboard homepage |
| `.lake/build/runway/dep_graph.html` | Dependency graph |
| `.lake/build/runway/manifest.json` | Precomputed stats + validation |
| `.lake/build/runway/paper.pdf` | Generated paper |

## Related Repos

| Repo | Purpose |
|------|---------|
| [Runway](https://github.com/e-vergo/Runway) | Site generator |
| [Dress](https://github.com/e-vergo/Dress) | Artifact generation |
| [LeanArchitect](https://github.com/e-vergo/LeanArchitect) | `@[blueprint]` attribute |
| [dress-blueprint-action](https://github.com/e-vergo/dress-blueprint-action) | CI/CD action |
| [General_Crystallographic_Restriction](https://github.com/e-vergo/General_Crystallographic_Restriction) | Production example |
| [PrimeNumberTheoremAnd](https://github.com/e-vergo/PrimeNumberTheoremAnd) | Large-scale integration |

## Live Site

[e-vergo.github.io/SBS-Test](https://e-vergo.github.io/SBS-Test/)
