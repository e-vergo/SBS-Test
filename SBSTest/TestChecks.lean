/-
SBS-Test: Graph Checks Test Fixtures
Tests: Cycle detection and disconnected component detection
-/
import Dress
import Mathlib.Data.Nat.Basic

namespace SBSTest.TestChecks

/-!
## Cycle Test

These two declarations form a dependency cycle for testing cycle detection.
They are mutually recursive - cycleA uses cycleB and cycleB uses cycleA.
-/

/-- CycleA: Part of a cycle for testing. Uses CycleB via metadata. -/
@[blueprint "thm:cycleA"
  (displayName := "Cycle Test A")
  (statement := /-- A trivial truth, part of a cycle test.
  \uses{thm:cycleB} -/)
  (uses := ["thm:cycleB"])
  (proof := /-- Uses cycleB in the proof, creating a cycle. -/)]
theorem cycleA : True := trivial

/-- CycleB: Part of a cycle for testing. Uses CycleA via metadata. -/
@[blueprint "thm:cycleB"
  (displayName := "Cycle Test B")
  (statement := /-- A trivial truth, part of a cycle test.
  \uses{thm:cycleA} -/)
  (uses := ["thm:cycleA"])
  (proof := /-- Uses cycleA in the proof, creating a cycle. -/)]
theorem cycleB : True := trivial

/-!
## Disconnected Test

This theorem is intentionally NOT connected to the rest of the graph.
Used to test disconnected component detection.
-/

/-- DisconnectedTheorem: Intentionally not connected to main graph.
    Used to test disconnected component detection. -/
@[blueprint "thm:disconnected"
  (displayName := "Disconnected Test")
  (statement := /-- $1 + 1 = 2$. This theorem has no dependencies. -/)
  (proof := /-- By reflexivity of equality. -/)]
theorem disconnectedTheorem : 1 + 1 = 2 := rfl

end SBSTest.TestChecks
