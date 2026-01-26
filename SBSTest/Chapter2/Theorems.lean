/-
SBS-Test: Chapter 2 - Theorems
Tests: Complex proofs, LaTeX math, cross-chapter dependencies
-/
import Dress
import SBSTest.Chapter1.Definitions
import SBSTest.Chapter1.Lemmas
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Int.Basic

namespace SBSTest.Chapter2

/-- Squares of integers are non-negative. -/
@[blueprint "thm:square-nonneg"
  (statement := /-- For any $x \in \mathbb{Z}$, we have $x^2 \geq 0$. -/)
  (proof := /-- Apply the lemma \texttt{sq\_nonneg}. -/)]
theorem square_nonneg (x : ℤ) : 0 ≤ x ^ 2 := sq_nonneg x

/-- Sum of two squares is non-negative. -/
@[blueprint "thm:sum-squares-nonneg"
  (statement := /-- For any $x, y \in \mathbb{Z}$, we have $x^2 + y^2 \geq 0$.
  \uses{thm:square-nonneg} -/)
  (uses := ["thm:square-nonneg"])
  (proof := /-- Both terms are non-negative by \texttt{square\_nonneg}. -/)]
theorem sum_squares_nonneg (x y : ℤ) : 0 ≤ x ^ 2 + y ^ 2 := by
  have h1 := square_nonneg x
  have h2 := square_nonneg y
  linarith

/-- The identity $(a+b)^2 = a^2 + 2ab + b^2$. -/
theorem binomial_square {R : Type*} [CommRing R] (a b : R) :
    (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring

end SBSTest.Chapter2
