/-
Verso blueprint document for SBS-Test.
Demonstrates the SBSBlueprint genre with hook directives.
-/
import SBSBlueprint
import SBSTest.StatusDemo

open Verso.Genre.SBSBlueprint

#doc (SBSBlueprint) "SBS-Test Blueprint" =>

# Introduction

This blueprint demonstrates the Side-by-Side Blueprint system. It shows how formal Lean proofs
can be displayed alongside LaTeX theorem statements, providing a unified view of both the
informal mathematical content and its formal verification.

The SBS-Test project contains 22 nodes across three branches, demonstrating all 6 status
colors, diamond merge patterns, and cross-branch dependencies.

# The Fully Proven Chain

The following theorems form a fully verified chain. Each node has a complete proof,
and all dependencies are also fully proven. This demonstrates the `fullyProven`
status, which is auto-computed by analyzing the dependency graph.

## Starting Point: The Leaf

Our chain begins with a proven leaf node that has no dependencies:

:::leanNode "proven_leaf"
:::

## Transitivity and Weakening

From this leaf, we build a chain of fully proven theorems:

:::leanNode "imp_trans"
:::

The weakening principle follows:

:::leanNode "weakening"
:::

## Diamond Pattern

The contrapositive and disjunction introduction create a diamond pattern
in the dependency graph:

:::leanNode "contrapositive"
:::

:::leanNode "disjunction_intro"
:::

# Theorems with Incomplete Proofs

Not all proofs are complete. The following theorems contain `sorry`, indicating
that work remains to be done. The system automatically detects this and marks
the nodes with the sorry status.

:::leanNode "add_zero"
:::

:::leanNode "add_comm"
:::

# Manual Status Flags

Some theorems have manual status flags that override auto-detection.

## Ready for Formalization

These theorems are marked as ready -- the proof strategy is clear:

:::leanNode "nat_identity"
:::

:::leanNode "set_basics"
:::

## Ready for Mathlib

This theorem is polished and ready for submission to mathlib:

:::leanNode "mathlib_ready"
:::

# Cross-Branch Merging

The core theorem merges the arithmetic and set theory branches:

:::leanNode "core_theorem"
:::

The synthesis merges all three branches:

:::leanNode "synthesis"
:::

# Full Module Reference

The following section includes all nodes from the ModuleRefTest module:

:::leanModule "SBSTest.ModuleRefTest"
:::
