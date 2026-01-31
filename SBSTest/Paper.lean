/-
Test Verso paper document for SBS-Test.
Demonstrates paper-style output with :::paperStatement, :::paperFull, :::paperProof hooks.
-/
import SBSBlueprint
import SBSTest.StatusDemo  -- For @[blueprint] declarations

open SBSBlueprint

#doc (SBSBlueprint) "SBS-Test Paper" =>

# Abstract

This paper demonstrates the Side-by-Side Blueprint paper generation system. We present
a collection of elementary propositions in propositional logic, establishing their formal
correctness via the Lean theorem prover. The integration of formal proofs with traditional
mathematical exposition enables direct verification of claimed results.

# Introduction

The formalization of mathematics has long been a goal of the mathematical community. With
modern proof assistants like Lean, we can now achieve machine-verified correctness for
mathematical proofs. This paper demonstrates the Side-by-Side Blueprint system, which
presents formal Lean proofs alongside their informal LaTeX statements.

Our main contributions are:
1. A proven identity function on propositions
2. A fully verified chain of implications
3. Transitivity of implication (mathlib-ready)

# Main Results

## The Identity Principle

We begin with the fundamental result that any proposition implies itself. This is the
cornerstone of our development.

:::paperStatement "proven_leaf"

The proof proceeds by direct implication introduction: given any proposition `P` and
a proof `h : P`, we simply return `h` as our proof of `P`. This result requires no
dependencies and forms the base of our fully proven chain.

## The Fully Proven Chain

Building on the identity principle, we establish a chain of fully verified theorems.
Each step in this chain has been mechanically verified, and the entire dependency
tree is complete.

:::paperFull "fully_chain_1"

The first theorem in our chain directly uses the proven leaf. Since its only dependency
is fully verified, this theorem automatically receives the "fully proven" status.

Continuing the chain, we establish a weakening principle:

:::paperStatement "fully_chain_2"

This demonstrates that from `P`, we can derive `Q → P` for any `Q`. The proof ignores
the hypothesis `Q` and returns the original proof of `P`.

## Transitivity of Implication

Our flagship result establishes the transitivity of logical implication. This theorem
meets mathlib quality standards and is ready for submission.

:::paperFull "mathlib_theorem"

The proof composes the two given implications: given `hPQ : P → Q` and `hQR : Q → R`
and a proof of `P`, we apply `hQR` to `hPQ hP` to obtain a proof of `R`.

# Incomplete Results

Not all proofs in a formalization project are complete. The following section documents
theorems that still contain gaps.

## Theorems with Sorry

The following theorem has an incomplete proof, indicated by the presence of `sorry`:

:::paperProof "has_sorry"

The sorry indicates that the proof of `∀ n : Nat, n + 0 = n` is not yet complete. While
this is a trivial fact in arithmetic (it follows by reflexivity), we intentionally leave
it incomplete to demonstrate the system's ability to detect and report sorry status.

# Discussion

The Side-by-Side Blueprint system provides a unified view of formal and informal
mathematics. Key features demonstrated in this paper include:

- **Statement extraction**: The `:::paperStatement` hook displays the LaTeX statement
  with a link to the formal Lean proof
- **Full side-by-side**: The `:::paperFull` hook shows both statement and Lean code
- **Proof extraction**: The `:::paperProof` hook extracts just the Lean proof body
- **Automatic status**: The system automatically detects sorry-containing proofs

Future work includes expanding the chain to more complex mathematical results and
integrating with the mathlib library.
