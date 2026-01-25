# SBS-Test

Test project for the Side-by-Side Blueprint pipeline.

This project demonstrates all features of the dress-blueprint tooling:
- `@[blueprint]` attribute annotations
- Syntax-highlighted Lean code with hover tooltips
- Proof toggle synchronization
- Multi-chapter blueprint structure
- Dependency graph generation
- GitHub Pages deployment via dress-blueprint-action

## Building Locally

```bash
lake exe cache get
BLUEPRINT_DRESS=1 lake build
lake build :blueprint
lake exe runway build runway.json
```

## Links

- [Blueprint Documentation](https://e-vergo.github.io/SBS-Test/)
- [dress-blueprint-action](https://github.com/e-vergo/dress-blueprint-action)
