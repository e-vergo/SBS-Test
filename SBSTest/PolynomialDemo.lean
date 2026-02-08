/-
Polynomial factoring demonstrations for KaTeX rendering test.

This module exists to provide rich LaTeX statements that exercise KaTeX's
math rendering in the Blueprint infoview panel. Each theorem has inline
and display math with varying complexity.
-/
import Dress
import Mathlib.Tactic

namespace SBSTest.PolynomialDemo

/-! ## Polynomial Factoring

Theorems about polynomial identities, used to test KaTeX rendering of
inline math ($...$) and display math ($$...$$) in the Blueprint panel.
-/

@[blueprint "poly:diff_squares"
  (title := "Difference of Squares")
  (statement := /-- For all integers $a$ and $b$, we have
  $a^2 - b^2 = (a - b)(a + b)$.

  This is the classical factoring identity. -/)
  (proof := /-- Both sides are polynomial expressions in $a$ and $b$; equality holds by expanding and cancelling like terms. -/)
  (message := "KaTeX test: inline math with superscripts and products")]
theorem diff_of_squares (a b : Int) : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by
  ring

@[blueprint "poly:perfect_square"
  (title := "Perfect Square Trinomial")
  (statement := /-- For all integers $x$,
  $$x^2 + 2x + 1 = (x + 1)^2.$$

  This is the expansion of a perfect square binomial. -/)
  (proof := /-- Expand $(x+1)^2$ to $x^2 + 2x + 1$ and verify the two polynomial expressions are identical. -/)
  (message := "KaTeX test: display math with $$")]
theorem perfect_square (x : Int) : x ^ 2 + 2 * x + 1 = (x + 1) ^ 2 := by
  ring

@[blueprint "poly:sum_cubes"
  (title := "Sum of Cubes")
  (uses := ["poly:diff_squares"])
  (statement := /-- The sum of cubes factors as
  $a^3 + b^3 = (a + b)(a^2 - ab + b^2)$
  for all integers $a, b$. -/)
  (proof := /-- Expand the right-hand side product and collect terms to verify it equals $a^3 + b^3$. -/)
  (message := "KaTeX test: cubed terms and multi-variable")]
theorem sum_of_cubes (a b : Int) : a ^ 3 + b ^ 3 = (a + b) * (a ^ 2 - a * b + b ^ 2) := by
  ring

end SBSTest.PolynomialDemo
