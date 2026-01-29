/-
SBS-Test: Simplified Status Demo
Demonstrates all 8 node statuses + disconnected cycle for validation testing.

Target: ~10 nodes total
- Main graph: 8 nodes showing all status types with dependencies
- Disconnected cycle: 2 nodes that reference each other (cycle + disconnected)
-/
import Dress
import Mathlib.Tactic

namespace SBSTest.StatusDemo

/-! ## Main Graph: 8 Status Types -/

-- 1. STATED: A definition with no proof needed (becomes "proven" since definitions are trivially complete)
-- Note: "stated" typically means LaTeX-only with no Lean code. For a Lean definition, use notReady.
@[blueprint "def:base"
  (title := "Base Definition")
  (statement := /-- A natural number $n$ is \emph{small} if $n < 10$. -/)]
def isSmall (n : Nat) : Prop := n < 10

-- 2. SORRY: Has sorry in the proof (derived status)
@[blueprint "thm:sorry"
  (title := "Sorry Example")
  (statement := /-- If $n$ is small, then $n + 1 \le 10$.
  \uses{def:base} -/)
  (uses := ["def:base"])
  (proof := /-- Proof incomplete - contains sorry. -/)]
theorem sorry_example (n : Nat) (h : isSmall n) : n + 1 ≤ 10 := by
  sorry

-- 3. PROVEN: Complete proof without sorry (derived status)
@[blueprint "thm:proven"
  (title := "Proven Theorem")
  (statement := /-- Zero is small.
  \uses{def:base} -/)
  (uses := ["def:base"])
  (proof := /-- By definition, $0 < 10$. -/)]
theorem zero_small : isSmall 0 := by
  unfold isSmall
  omega

-- 4. FULLY PROVEN: Manual flag (typically auto-computed from graph)
@[blueprint "thm:fullyproven" (fullyProven := true)
  (title := "Fully Proven")
  (statement := /-- One is small.
  \uses{thm:proven} -/)
  (uses := ["thm:proven"])
  (proof := /-- Follows from zero being small. -/)]
theorem one_small : isSmall 1 := by
  unfold isSmall
  omega

-- 5. KEY THEOREM: Marked as key declaration for dashboard
@[blueprint "thm:key" (keyDeclaration := true)
  (title := "Key Result")
  (statement := /-- Two is small - a key result.
  \uses{thm:fullyproven} -/)
  (uses := ["thm:fullyproven"])
  (proof := /-- Straightforward from definition. -/)]
theorem two_small : isSmall 2 := by
  unfold isSmall
  omega

-- 6. BLOCKED: Waiting on external work
@[blueprint "thm:blocked" (blocked := "Waiting for mathlib PR #12345")
  (title := "Blocked Theorem")
  (statement := /-- Three is small.
  \uses{thm:key} -/)
  (uses := ["thm:key"])
  (proof := /-- Cannot proceed until upstream is merged. -/)]
theorem three_small : isSmall 3 := by
  unfold isSmall
  omega

-- 7. POTENTIAL ISSUE: Has known concerns
@[blueprint "thm:issue" (potentialIssue := "May not generalize to larger bounds")
  (title := "Issue Example")
  (statement := /-- Four is small.
  \uses{thm:blocked} -/)
  (uses := ["thm:blocked"])
  (proof := /-- Direct computation. -/)]
theorem four_small : isSmall 4 := by
  unfold isSmall
  omega

-- 8. TECHNICAL DEBT: Needs refactoring
@[blueprint "thm:debt" (technicalDebt := "Refactor to use Nat.lt_of_lt_of_le")
  (title := "Technical Debt")
  (statement := /-- Five is small.
  \uses{thm:issue} -/)
  (uses := ["thm:issue"])
  (proof := /-- Should use better lemmas. -/)]
theorem five_small : isSmall 5 := by
  unfold isSmall
  omega

/-! ## Disconnected Cycle: 2 Mutually Referencing Nodes

These nodes form a cycle (A -> B -> A) and are NOT connected to the main graph.
This tests both cycle detection and disconnected component detection.
-/

-- 9. CYCLE A: Uses Cycle B
@[blueprint "thm:cycleA"
  (title := "Cycle A")
  (statement := /-- First half of a cyclic dependency.
  \uses{thm:cycleB} -/)
  (uses := ["thm:cycleB"])
  (proof := /-- Trivial, but creates a cycle with cycleB. -/)]
theorem cycleA : True := trivial

-- 10. CYCLE B: Uses Cycle A
@[blueprint "thm:cycleB"
  (title := "Cycle B")
  (statement := /-- Second half of a cyclic dependency.
  \uses{thm:cycleA} -/)
  (uses := ["thm:cycleA"])
  (proof := /-- Trivial, but creates a cycle with cycleA. -/)]
theorem cycleB : True := trivial

/-! ## Additional Status Demos (for completeness) -/

-- NOT READY: Not ready to formalize
@[blueprint "thm:notready" (notReady := true)
  (title := "Not Ready")
  (statement := /-- A future theorem not ready for formalization. -/)]
theorem not_ready_example : True := trivial

-- READY: Ready to formalize (has sorry but marked ready)
@[blueprint "thm:ready" (ready := true)
  (title := "Ready to Prove")
  (statement := /-- Ready for someone to prove.
  \uses{def:base} -/)
  (uses := ["def:base"])
  (proof := /-- Awaiting proof. -/)]
theorem ready_example (n : Nat) : isSmall n → n < 100 := by
  sorry

-- MATHLIB READY: Ready to upstream
@[blueprint "thm:mathlibready" (mathlibReady := true)
  (title := "Mathlib Ready")
  (statement := /-- Ready to submit to Mathlib.
  \uses{thm:proven} -/)
  (uses := ["thm:proven"])
  (proof := /-- Complete and polished. -/)]
theorem mathlib_ready_example : isSmall 6 := by
  unfold isSmall
  omega

-- IN MATHLIB: Already in Mathlib
@[blueprint "thm:inmathlib" (mathlib := true)
  (title := "In Mathlib")
  (statement := /-- This exists in Mathlib (simulated). -/)]
theorem in_mathlib_example : 1 + 1 = 2 := rfl

end SBSTest.StatusDemo
