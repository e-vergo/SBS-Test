/-
SBS-Test: Status Demo
Demonstrates all 8 node status colors + disconnected cycle for validation testing.

The 8 status colors:
1. notReady    - Manual: not ready to formalize (red/gray)
2. stated      - Default: has blueprint statement only (light blue)
3. ready       - Manual: ready to formalize (orange)
4. sorry       - Derived: proof contains sorry (yellow)
5. proven      - Derived: complete proof without sorry (light green)
6. fullyProven - Manual/auto: this + all deps proven (dark green)
7. mathlibReady- Manual: ready to upstream to Mathlib (purple)
8. inMathlib   - Manual: already in Mathlib (dark blue)

Target: 10 main nodes + 2 disconnected cycle nodes
-/
import Dress
import Mathlib.Tactic

namespace SBSTest.StatusDemo

/-! ## Main Graph: All 8 Status Colors

Chain structure: base -> notready -> stated -> ready -> sorry -> proven -> fullyproven -> mathlibready -> inmathlib
-/

-- Base definition that all others depend on
@[blueprint "def:base"
  (title := "Base Definition")
  (statement := /-- A natural number $n$ is \emph{small} if $n < 10$. -/)]
def isSmall (n : Nat) : Prop := n < 10

/-! ### Status 1: NOT READY (red/gray) -/
-- Manual flag: (notReady := true)
-- Indicates node is not ready to be formalized yet
@[blueprint "thm:notready" (notReady := true)
  (title := "Not Ready Example")
  (statement := /-- A theorem that is not ready for formalization.
  \uses{def:base} -/)
  (uses := ["def:base"])]
theorem notready_example : isSmall 0 := by unfold isSmall; omega

/-! ### Status 2: STATED (light blue) -/
-- Default status: no manual flags, just the blueprint statement
-- Normally this would have no Lean implementation, but we include one for the graph
@[blueprint "thm:stated"
  (title := "Stated Example")
  (statement := /-- A theorem that is merely stated in the blueprint.
  \uses{thm:notready} -/)
  (uses := ["thm:notready"])
  (proof := /-- No proof provided yet. -/)]
theorem stated_example : isSmall 1 := by unfold isSmall; omega

/-! ### Status 3: READY (orange) -/
-- Manual flag: (ready := true)
-- Indicates node is ready to be formalized by a contributor
@[blueprint "thm:ready" (ready := true)
  (title := "Ready Example")
  (statement := /-- A theorem ready for someone to prove.
  \uses{thm:stated} -/)
  (uses := ["thm:stated"])
  (proof := /-- Ready for formalization! -/)]
theorem ready_example : isSmall 2 := by unfold isSmall; omega

/-! ### Status 4: SORRY (yellow) -/
-- Derived status: proof contains `sorry`
-- Automatically detected from the Lean code
@[blueprint "thm:sorry"
  (title := "Sorry Example")
  (statement := /-- A theorem with an incomplete proof.
  \uses{thm:ready} -/)
  (uses := ["thm:ready"])
  (proof := /-- Proof incomplete - contains sorry. -/)]
theorem sorry_example : isSmall 3 := by
  sorry

/-! ### Status 5: PROVEN (light green) -/
-- Derived status: complete proof without sorry
-- Automatically detected from the Lean code
@[blueprint "thm:proven"
  (title := "Proven Example")
  (statement := /-- A theorem with a complete proof.
  \uses{thm:sorry} -/)
  (uses := ["thm:sorry"])
  (proof := /-- Complete proof by omega. -/)]
theorem proven_example : isSmall 4 := by
  unfold isSmall
  omega

/-! ### Status 6: FULLY PROVEN (dark green) -/
-- Manual flag: (fullyProven := true)
-- Indicates this theorem AND all its dependencies are proven
-- Can also be auto-computed from the dependency graph
@[blueprint "thm:fullyproven" (fullyProven := true)
  (title := "Fully Proven Example")
  (statement := /-- A theorem where the full dependency chain is proven.
  \uses{thm:proven} -/)
  (uses := ["thm:proven"])
  (proof := /-- This and all ancestors are proven. -/)]
theorem fullyproven_example : isSmall 5 := by
  unfold isSmall
  omega

/-! ### Status 7: MATHLIB READY (purple) -/
-- Manual flag: (mathlibReady := true)
-- Indicates this theorem is polished and ready for Mathlib upstream
@[blueprint "thm:mathlibready" (mathlibReady := true)
  (title := "Mathlib Ready Example")
  (statement := /-- A theorem ready to be upstreamed to Mathlib.
  \uses{thm:fullyproven} -/)
  (uses := ["thm:fullyproven"])
  (proof := /-- Polished and ready for contribution. -/)]
theorem mathlibready_example : isSmall 6 := by
  unfold isSmall
  omega

/-! ### Status 8: IN MATHLIB (dark blue) -/
-- Manual flag: (mathlib := true)
-- Indicates this result already exists in Mathlib
@[blueprint "thm:inmathlib" (mathlib := true)
  (title := "In Mathlib Example")
  (statement := /-- A theorem that exists in Mathlib.
  \uses{thm:mathlibready} -/)
  (uses := ["thm:mathlibready"])]
theorem inmathlib_example : isSmall 7 := by
  unfold isSmall
  omega

/-! ## Disconnected Cycle: Validation Testing

These nodes form a cycle (A -> B -> A) and are NOT connected to the main graph.
This tests both cycle detection and disconnected component detection.
-/

@[blueprint "thm:cycleA"
  (title := "Cycle A")
  (statement := /-- First half of a cyclic dependency.
  \uses{thm:cycleB} -/)
  (uses := ["thm:cycleB"])
  (proof := /-- Creates a cycle with cycleB. -/)]
theorem cycleA : True := trivial

@[blueprint "thm:cycleB"
  (title := "Cycle B")
  (statement := /-- Second half of a cyclic dependency.
  \uses{thm:cycleA} -/)
  (uses := ["thm:cycleA"])
  (proof := /-- Creates a cycle with cycleA. -/)]
theorem cycleB : True := trivial

end SBSTest.StatusDemo
