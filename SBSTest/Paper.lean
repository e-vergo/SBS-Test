/-
Verso paper document for SBS-Test.
Demonstrates paper-style output with :::paperStatement, :::paperFull, :::paperProof hooks.
-/
import SBSBlueprint
import SBSTest.StatusDemo

open Verso.Genre.SBSBlueprint

#doc (SBSBlueprint) "SBS-Test Paper" =>

# Abstract

This paper demonstrates the Side-by-Side Blueprint paper generation system. We present
a structured dependency graph with three branches of mathematical results, establishing
their formal correctness via the Lean theorem prover. The integration of formal proofs
with traditional mathematical exposition enables direct verification of claimed results.

# Introduction

The formalization of mathematics has long been a goal of the mathematical community. With
modern proof assistants like Lean, we can now achieve machine-verified correctness for
mathematical proofs. This paper demonstrates the Side-by-Side Blueprint system, which
presents formal Lean proofs alongside their informal LaTeX statements.

Our main contributions are:
1. A fully verified chain of propositional logic theorems
2. Demonstration of sorry propagation through arithmetic results
3. A mathlib-ready theorem on the clean dependency chain

# Main Results

## The Identity Principle

We begin with the fundamental result that any proposition implies itself. This is the
cornerstone of our fully verified chain.

:::paperStatement "proven_leaf"
:::

The proof proceeds by direct implication introduction: given any proposition `P` and
a proof `h : P`, we simply return `h` as our proof of `P`.

## The Fully Proven Chain

Building on the identity principle, we establish transitivity of implication:

:::paperFull "imp_trans"
:::

The weakening principle follows, demonstrating that from `P`, we can derive
`Q -> P` for any `Q`:

:::paperStatement "weakening"
:::

## Diamond Pattern

The contrapositive and disjunction introduction create a diamond in the
dependency graph, both depending on imp_trans:

:::paperFull "disjunction_intro"
:::

## Core Theorem

The core theorem merges the arithmetic and set theory branches:

:::paperFull "core_theorem"
:::

## Mathlib-Ready Theorem

Our flagship result establishes a theorem ready for mathlib submission,
depending only on the fully verified chain:

:::paperFull "mathlib_ready"
:::

# Incomplete Results

Not all proofs in a formalization project are complete. The following section documents
theorems that still contain gaps.

## Theorems with Sorry

The following theorem has an incomplete proof, indicated by the presence of `sorry`:

:::paperProof "add_zero"
:::

The sorry indicates that the proof of the left identity of addition is not yet
complete. We intentionally leave it incomplete to demonstrate the system's
ability to detect and report sorry status.

# Discussion

The Side-by-Side Blueprint system provides a unified view of formal and informal
mathematics. Key features demonstrated in this paper include:

- **Statement extraction**: The `:::paperStatement` hook displays the LaTeX statement
  with a link to the formal Lean proof
- **Full side-by-side**: The `:::paperFull` hook shows both statement and Lean code
- **Proof extraction**: The `:::paperProof` hook extracts just the Lean proof body
- **Automatic status**: The system automatically detects sorry-containing proofs
- **Diamond patterns**: Cross-branch dependencies create rich DAG structures
