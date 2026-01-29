/-
SBS-Test: Chapter 4 - Status Testing
Tests: All 8 blueprint node statuses for dependency graph visualization
-/
import Dress
import Mathlib.Tactic

namespace SBSTest.Chapter4

/-!
# Parity Definitions and Theorems

This module tests all 8 blueprint node statuses using parity-themed declarations.

## Status Categories:

**Manual statuses** (set via attribute options):
- `notReady`: Not ready to formalize
- `ready`: Ready to formalize
- `mathlibReady`: Ready to upstream to Mathlib
- `inMathlib`: Already in Mathlib (manual override)

**Default status**:
- `stated`: Default when no manual status is set

**Derived statuses** (computed automatically):
- `sorry`: Has sorryAx in proof
- `proven`: Formalized without sorry
- `fullyProven`: This + all dependencies proven (auto-computed)
-/

-- ============================================================================
-- Status: inMathlib (manual override via mathlib := true)
-- Color: Dark blue (#1e3a5f)
-- ============================================================================

/-- A natural number is even if it's divisible by 2. -/
@[blueprint "def:even" (mathlib := true)
  (statement := /-- A natural number $n$ is \emph{even} if there exists $k$ such that $n = 2k$.
  \uses{def:double} -/)
  (uses := ["def:double"])]
def Even (n : Nat) : Prop := exists k, n = 2 * k

-- ============================================================================
-- Status: mathlibReady (manual via mathlibReady := true, needs complete proof)
-- Color: Medium blue (#4a90d9)
-- ============================================================================

/-- A natural number is odd if it's not even. -/
@[blueprint "def:odd" (mathlibReady := true)
  (statement := /-- A natural number $n$ is \emph{odd} if it is not even.
  \uses{def:even} -/)
  (uses := ["def:even"])]
def Odd (n : Nat) : Prop := Not (Even n)

-- ============================================================================
-- Status: proven (derived - complete proof without sorry)
-- Color: Green (#4caf50)
-- ============================================================================

/-- The sum of two even numbers is even. -/
@[blueprint "thm:even-add-even"
  (statement := /-- The sum of two even numbers is even.
  \uses{def:even} -/)
  (uses := ["def:even"])
  (proof := /-- Direct calculation using the definition of even. -/)]
theorem even_add_even (a b : Nat) (ha : Even a) (hb : Even b) : Even (a + b) := by
  obtain ⟨k, hk⟩ := ha
  obtain ⟨j, hj⟩ := hb
  exact ⟨k + j, by omega⟩

-- ============================================================================
-- Status: sorry (derived - has sorry in proof)
-- Color: Orange (#ff9800)
-- ============================================================================

/-- The sum of two odd numbers is even. -/
@[blueprint "thm:odd-add-odd"
  (statement := /-- The sum of two odd numbers is even.
  \uses{def:odd} -/)
  (uses := ["def:odd"])
  (proof := /-- This proof is incomplete and contains sorry. -/)]
theorem odd_add_odd (a b : Nat) (ha : Odd a) (hb : Odd b) : Even (a + b) := by
  sorry

-- ============================================================================
-- Status: fullyProven (auto-computed: this + all dependencies are proven)
-- Color: Dark green (#2e7d32)
-- This requires the theorem AND all its dependencies to be fully proven.
-- Since even_add_even depends on def:even (inMathlib), and even_add_even is proven,
-- a theorem depending ONLY on even_add_even should become fullyProven.
-- ============================================================================

/-- An even number times any number is even. -/
@[blueprint "thm:even-times-any"
  (statement := /-- If $a$ is even, then $a \cdot b$ is even for any $b$.
  \uses{def:even} -/)
  (uses := ["def:even"])
  (proof := /-- Unfold the definition and use associativity of multiplication. -/)]
theorem even_times_any (a b : Nat) (ha : Even a) : Even (a * b) := by
  obtain ⟨k, hk⟩ := ha
  exact ⟨k * b, by rw [hk]; ring⟩

/-- Zero is even - a simple standalone proven theorem.
    Marked as fullyProven since it and all its dependencies are complete.
    Note: Uses (fullyProven := true) which requires rebuilt LeanArchitect. -/
@[blueprint "thm:zero-even" (fullyProven := true)
  (statement := /-- Zero is even.
  \uses{def:even} -/)
  (uses := ["def:even"])
  (proof := /-- Trivially, $0 = 2 \cdot 0$. -/)]
theorem zero_even : Even 0 := ⟨0, by ring⟩

-- ============================================================================
-- Status: notReady (manual via notReady := true)
-- Color: Gray (#9e9e9e)
-- ============================================================================

/-- A future theorem about parity and primes. -/
theorem future_parity_prime : True := trivial  -- placeholder

-- ============================================================================
-- Status: stated (default - no manual status, but has Lean decl)
-- Note: "stated" typically means blueprint entry exists but no Lean implementation.
-- When there IS a Lean implementation, the status may be overridden to proven/sorry.
-- For testing, we use a trivial placeholder that should still show as proven.
-- ============================================================================

/-- A planned lemma about consecutive integers. -/
@[blueprint "lem:consecutive-parity"
  (statement := /-- Of any two consecutive integers, exactly one is even.
  \uses{def:even, def:odd} -/)
  (uses := ["def:even", "def:odd"])]
theorem consecutive_parity : True := trivial  -- Becomes proven since no sorry

-- ============================================================================
-- Status: ready (manual via ready := true)
-- Color: Light blue (#90caf9)
-- ============================================================================

/-- Ready to prove: alternating parity.
    This uses `sorry` but is marked `ready := true`, so it should show TEAL, not orange. -/
@[blueprint "thm:alternating-parity" (ready := true)
  (statement := /-- The sequence $n, n+1, n+2, \ldots$ alternates in parity.
  \uses{lem:consecutive-parity} -/)
  (uses := ["lem:consecutive-parity"])
  (proof := /-- Proof is in progress. -/)]
theorem alternating_parity (n : Nat) : (Even n ∧ Odd (n+1)) ∨ (Odd n ∧ Even (n+1)) := by
  sorry  -- Marked ready, so should show TEAL despite sorry

-- ============================================================================
-- Additional test cases for dependency chains
-- ============================================================================

/-- A theorem with multiple dependencies including a sorry node. -/
@[blueprint "thm:mixed-deps"
  (statement := /-- A result depending on both proven and sorry nodes.
  \uses{thm:even-add-even, thm:odd-add-odd} -/)
  (uses := ["thm:even-add-even", "thm:odd-add-odd"])
  (proof := /-- Incomplete proof with mixed dependencies. -/)]
theorem mixed_deps (n : Nat) : Even n ∨ Odd n := by
  sorry

/-- Ultimate goal theorem with deep dependency chain. -/
@[blueprint "thm:goal-parity" (notReady := true)
  (statement := /-- The fundamental theorem of parity.
  \uses{thm:mixed-deps} -/)
  (uses := ["thm:mixed-deps"])]
theorem goal_parity : True := trivial  -- placeholder

/-- A mathlibReady theorem with complete proof. -/
@[blueprint "thm:double-even" (mathlibReady := true)
  (statement := /-- Double any number is even.
  \uses{def:even} -/)
  (uses := ["def:even"])
  (proof := /-- By definition, $2n = 2 \cdot n$. -/)]
theorem double_even (n : Nat) : Even (2 * n) := ⟨n, rfl⟩

-- ============================================================================
-- Dashboard Feature Tests
-- Tests for: keyDeclaration, message, priority, blocked, potentialIssue,
--            technicalDebt, misc
-- ============================================================================

/-- A key theorem that should appear in the Key Theorems dashboard panel. -/
@[blueprint "thm:dashboard-key" (keyDeclaration := true)
  (statement := /-- This is a key theorem for testing the dashboard feature.
  It should appear in the Key Theorems panel.
  \uses{thm:even-add-even} -/)
  (uses := ["thm:even-add-even"])]
theorem dashboard_key_theorem : 1 + 1 = 2 := rfl

/-- A theorem with a user message note. -/
@[blueprint "thm:dashboard-message" (message := "Consider alternative proof approach")
  (statement := /-- A theorem with a message annotation for the dashboard.
  \uses{thm:dashboard-key} -/)
  (uses := ["thm:dashboard-key"])]
lemma dashboard_message_test : True := trivial

/-- A high-priority item that should appear in Priority Items dashboard. -/
@[blueprint "thm:dashboard-priority-high" (priorityItem := true)
  (statement := /-- A high-priority theorem for urgent attention.
  \uses{thm:double-even} -/)
  (uses := ["thm:double-even"])]
theorem dashboard_priority_high : True := trivial

/-- Another priority item for testing. -/
@[blueprint "thm:dashboard-priority-medium" (priorityItem := true)
  (statement := /-- Another priority item.
  \uses{thm:dashboard-priority-high} -/)
  (uses := ["thm:dashboard-priority-high"])]
theorem dashboard_priority_medium : True := trivial

/-- A blocked theorem waiting for upstream work. -/
@[blueprint "thm:dashboard-blocked" (blocked := "Waiting for upstream mathlib PR")
  (statement := /-- A blocked theorem that cannot proceed yet.
  \uses{def:even} -/)
  (uses := ["def:even"])]
theorem dashboard_blocked_test : True := trivial

/-- A theorem with potential issues noted. -/
@[blueprint "lem:dashboard-issue" (potentialIssue := "May not generalize to infinite case")
  (statement := /-- A lemma with a potential issue flag.
  \uses{thm:even-times-any} -/)
  (uses := ["thm:even-times-any"])]
lemma dashboard_issue_test : True := trivial

/-- A definition with technical debt. -/
@[blueprint "def:dashboard-debt" (technicalDebt := "Refactor to use Finset API")
  (statement := /-- A definition that has technical debt notes.
  \uses{def:even} -/)
  (uses := ["def:even"])]
def dashboard_debt_test : Nat := 42

/-- A theorem with miscellaneous notes. -/
@[blueprint "thm:dashboard-misc" (misc := "See discussion in issue #42")
  (statement := /-- A theorem with miscellaneous notes.
  \uses{def:dashboard-debt} -/)
  (uses := ["def:dashboard-debt"])]
theorem dashboard_misc_test : True := trivial

/-- A theorem with multiple dashboard annotations. -/
@[blueprint "thm:dashboard-multi" (keyDeclaration := true) (priorityItem := true)
  (message := "Critical path theorem") (potentialIssue := "Needs review")
  (statement := /-- A key theorem with multiple dashboard flags.
  \uses{thm:dashboard-misc, lem:dashboard-issue} -/)
  (uses := ["thm:dashboard-misc", "lem:dashboard-issue"])]
theorem dashboard_multi_flags : 2 + 2 = 4 := rfl

end SBSTest.Chapter4
