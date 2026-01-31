/-
Test Verso blueprint document for SBS-Test.
Demonstrates the SBSBlueprint genre with hook directives.
-/
import SBSBlueprint
import SBSTest.StatusDemo  -- For @[blueprint] declarations

open SBSBlueprint

#doc (SBSBlueprint) "SBS-Test Blueprint" =>

# Introduction

This blueprint demonstrates the Side-by-Side Blueprint system. It shows how formal Lean proofs
can be displayed alongside LaTeX theorem statements, providing a unified view of both the
informal mathematical content and its formal verification.

The SBS-Test project contains 15 nodes demonstrating all 6 status colors and validation
features like cycle detection and disconnected component detection.

# The Fully Proven Chain

The following theorems form a fully verified chain. Each node in this chain has a complete
proof, and all dependencies are also fully proven. This demonstrates the `fullyProven`
status, which is auto-computed by analyzing the dependency graph.

## Starting Point: The Leaf

Our chain begins with a proven leaf node that has no dependencies:

:::leanNode "proven_leaf"

## Building the Chain

From this leaf, we build a chain of fully proven theorems:

:::leanNode "fully_chain_1"

This continues through the chain:

:::leanNode "fully_chain_2"

And reaches its conclusion:

:::leanNode "fully_chain_3"

# Theorems with Incomplete Proofs

Not all proofs are complete. The following theorem contains a `sorry`, indicating
that work remains to be done. The system automatically detects this and marks the
node with the "sorry" status.

:::leanNode "has_sorry"

Nodes with sorry block downstream verification. Even if a theorem has a complete
proof structure, if it depends on a sorry node, it cannot be marked as fully proven.

:::leanNode "also_sorry"

# Manual Status Flags

Some theorems have manual status flags that override the auto-detection.

## Ready for Formalization

This theorem is marked as "ready" -- the proof strategy is clear, we just need
to write the Lean code:

:::leanNode "ready_to_prove"

## Ready for Mathlib

This theorem is polished and ready for submission to mathlib:

:::leanNode "mathlib_theorem"

# Dependency Cycles

The following nodes form a cycle, which is usually a sign of a logical error
in the blueprint structure:

:::leanNode "cycle_a"

:::leanNode "cycle_b"

# Full Module Reference

The following section includes all nodes from the StatusDemo module:

:::leanModule "SBSTest.StatusDemo"
