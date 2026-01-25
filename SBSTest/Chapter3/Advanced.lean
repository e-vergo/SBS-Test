/-
SBS-Test: Chapter 3 - Advanced Topics
Tests: Mixed proof styles, deeper dependencies
-/
import Dress
import SBSTest.Chapter1.Definitions
import SBSTest.Chapter2.Theorems
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace SBSTest.Chapter3

open SBSTest.Chapter1

/-- Two is prime. -/
@[blueprint "thm:two-prime"
  (statement := /-- The number $2$ is prime. -/)
  (proof := /-- Standard fact from Mathlib. -/)]
theorem two_prime : Nat.Prime 2 := Nat.prime_two

/-- Three is prime. -/
@[blueprint "thm:three-prime"
  (statement := /-- The number $3$ is prime. -/)
  (proof := /-- Standard fact from Mathlib. -/)]
theorem three_prime : Nat.Prime 3 := Nat.prime_three

/-- All primes greater than 2 are odd - multi-step tactic proof. -/
@[blueprint "thm:odd-prime"
  (statement := /-- If $p > 2$ is prime, then $p$ is odd.
  \uses{thm:two-prime} -/)
  (uses := ["thm:two-prime"])
  (proof := /-- By contradiction: if $p$ is even, then $2 \mid p$, so $p = 2$. -/)]
theorem odd_prime (p : ℕ) (hp : Nat.Prime p) (hp2 : p > 2) : Odd p := by
  by_contra h
  rw [Nat.not_odd_iff_even, Nat.even_iff] at h
  have hdvd : 2 ∣ p := ⟨p / 2, by omega⟩
  have := hp.eq_one_or_self_of_dvd 2 hdvd
  omega

/-- Combining results: double of a successor is positive. -/
@[blueprint "cor:double-succ-positive"
  (statement := /-- For any $n$, $2(n+1) > 0$.
  \uses{thm:succ-positive, lem:double-positive} -/)
  (uses := ["thm:succ-positive", "lem:double-positive"])
  (proof := /-- Combine successor positivity with doubling preservation. -/)]
theorem double_succ_positive (n : ℕ) : isPositive (double (n + 1)) :=
  double_positive (n + 1) (succ_positive n)

end SBSTest.Chapter3
