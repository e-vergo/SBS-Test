/-
SBS-Test: Chapter 1 - Definitions
Tests: @[blueprint] attribute, definitions, term mode proofs
-/
import Dress
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

namespace SBSTest.Chapter1

/-- A simple predicate for testing. -/
@[blueprint "def:is-positive"
  (statement := /-- A natural number $n$ is \emph{positive} if $n > 0$. -/)]
def isPositive (n : ℕ) : Prop := n > 0

/-- The successor of any natural is positive - term mode proof. -/
@[blueprint "thm:succ-positive"
  (statement := /-- For any $n \in \mathbb{N}$, $n + 1 > 0$.
  \uses{def:is-positive} -/)
  (uses := ["def:is-positive"])
  (proof := /-- Direct application of successor properties. -/)]
theorem succ_positive (n : ℕ) : isPositive (n + 1) := Nat.succ_pos n

/-- Double a number. -/
@[blueprint "def:double"
  (statement := /-- Define $\mathrm{double}(n) = 2n$. -/)]
def double (n : ℕ) : ℕ := 2 * n

/-- Doubling preserves positivity - term mode. -/
@[blueprint "lem:double-positive"
  (statement := /-- If $n > 0$, then $2n > 0$.
  \uses{def:is-positive, def:double} -/)
  (uses := ["def:is-positive", "def:double"])
  (proof := /-- Multiplication by 2 preserves positivity. -/)]
lemma double_positive (n : ℕ) (h : isPositive n) : isPositive (double n) :=
  Nat.mul_pos (by norm_num : 0 < 2) h

end SBSTest.Chapter1
