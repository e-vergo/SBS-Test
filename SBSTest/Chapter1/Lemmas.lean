/-
SBS-Test: Chapter 1 - Lemmas
Tests: Tactic mode proofs, proof toggle synchronization
-/
import Dress
import SBSTest.Chapter1.Definitions
import Mathlib.Tactic

namespace SBSTest.Chapter1

/-- Adding two positive numbers gives a positive result - tactic mode. -/
@[blueprint "lem:add-positive"
  (statement := /-- If $m > 0$ and $n > 0$, then $m + n > 0$.
  \uses{def:is-positive} -/)
  (uses := ["def:is-positive"])
  (proof := /-- By cases and arithmetic. -/)]
lemma add_positive (m n : ℕ) (hm : isPositive m) (hn : isPositive n) :
    isPositive (m + n) := by
  unfold isPositive at *
  omega

/-- Positivity is preserved under maximum - longer tactic proof. -/
@[blueprint "lem:max-positive"
  (statement := /-- If $m > 0$ or $n > 0$, then $\max(m, n) > 0$.
  \uses{def:is-positive} -/)
  (uses := ["def:is-positive"])
  (proof := /-- Case analysis on which argument provides positivity. -/)]
lemma max_positive (m n : ℕ) (h : isPositive m ∨ isPositive n) :
    isPositive (max m n) := by
  unfold isPositive at *
  rcases h with hm | hn
  · calc max m n ≥ m := le_max_left m n
      _ > 0 := hm
  · calc max m n ≥ n := le_max_right m n
      _ > 0 := hn

end SBSTest.Chapter1
