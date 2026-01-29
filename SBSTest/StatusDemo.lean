/-
SBS-Test: Status Demo
Demonstrates all 8 node status colors + dashboard metadata features.

## Status Colors:
1. notReady    - Manual: not ready to formalize (red/gray)
2. stated      - Default: has blueprint statement only (light blue)
3. ready       - Manual: ready to formalize (orange)
4. sorry       - Derived: proof contains sorry (yellow)
5. proven      - Derived: complete proof without sorry (light green)
6. fullyProven - Manual/auto: this + all deps proven (dark green)
7. mathlibReady- Manual: ready to upstream to Mathlib (purple)
8. inMathlib   - Manual: already in Mathlib (dark blue)

## Dashboard Metadata:
- keyDeclaration: Highlight in Key Theorems panel
- message: Notes shown in Messages panel
- priorityItem: Flag for Priority Items column
- blocked: Blockage reason in Blocked column
- potentialIssue: Known concerns
- technicalDebt: Cleanup notes
- misc: Catch-all notes
-/
import Dress
import Mathlib.Tactic

namespace SBSTest.StatusDemo

/-! ## Main Graph: All 8 Status Colors

Tree structure:
```
              def:base
           /     |     \
    notready  stated   ready
                 |       |
               sorry     |
                 \      /
                 proven
                    |
              fullyproven
                    |
              mathlibready
                    |
               inmathlib
```
-/

-- Base definition - hub that others depend on
@[blueprint "def:base"
  (title := "Base Definition")
  (message := "Core definition - all theorems depend on this")
  (statement := /-- A natural number $n$ is \emph{small} if $n < 10$. -/)]
def isSmall (n : Nat) : Prop := n < 10

/-! ### Status 1: NOT READY (red/gray) -/
@[blueprint "thm:notready" (notReady := true)
  (title := "Not Ready Example")
  (priorityItem := true)
  (potentialIssue := "Need to clarify the bound - should it be strict?")
  (statement := /-- A theorem not ready for formalization. \uses{def:base} -/)
  (uses := ["def:base"])]
theorem notready_example : isSmall 0 := by unfold isSmall; omega

/-! ### Status 2: STATED (light blue) -/
@[blueprint "thm:stated"
  (title := "Stated Example")
  (misc := "Consider using a different approach via Nat.lt_of_succ_le")
  (statement := /-- A theorem merely stated. \uses{def:base} -/)
  (uses := ["def:base"])
  (proof := /-- No proof yet. -/)]
theorem stated_example : isSmall 1 := by unfold isSmall; omega

/-! ### Status 3: READY (orange) -/
@[blueprint "thm:ready" (ready := true)
  (title := "Ready Example")
  (technicalDebt := "Proof uses omega but could be simplified to decide")
  (statement := /-- A theorem ready to prove. \uses{def:base} -/)
  (uses := ["def:base"])
  (proof := /-- Ready for formalization! -/)]
theorem ready_example : isSmall 2 := by unfold isSmall; omega

/-! ### Status 4: SORRY (yellow) -/
@[blueprint "thm:sorry"
  (title := "Sorry Example")
  (blocked := "Waiting for upstream lemma in Mathlib")
  (priorityItem := true)
  (statement := /-- An incomplete proof. \uses{thm:stated} -/)
  (uses := ["thm:stated"])
  (proof := /-- Contains sorry. -/)]
theorem sorry_example : isSmall 3 := by
  sorry

/-! ### Status 5: PROVEN (light green) -/
@[blueprint "thm:proven"
  (title := "Proven Example")
  (keyDeclaration := true)
  (message := "Main convergence theorem - key milestone!")
  (statement := /-- A complete proof. \uses{thm:sorry, thm:ready} -/)
  (uses := ["thm:sorry", "thm:ready"])
  (proof := /-- Complete proof. -/)]
theorem proven_example : isSmall 4 := by
  unfold isSmall
  omega

/-! ### Status 6: FULLY PROVEN (dark green) -/
@[blueprint "thm:fullyproven" (fullyProven := true)
  (title := "Fully Proven Example")
  (keyDeclaration := true)
  (message := "Complete with all dependencies - ready for production use")
  (statement := /-- Full dependency chain proven. \uses{thm:proven} -/)
  (uses := ["thm:proven"])
  (proof := /-- All ancestors proven. -/)]
theorem fullyproven_example : isSmall 5 := by
  unfold isSmall
  omega

/-! ### Status 7: MATHLIB READY (purple) -/
@[blueprint "thm:mathlibready" (mathlibReady := true)
  (title := "Mathlib Ready Example")
  (statement := /-- Ready to upstream. \uses{thm:fullyproven} -/)
  (uses := ["thm:fullyproven"])
  (proof := /-- Polished for Mathlib. -/)]
theorem mathlibready_example : isSmall 6 := by
  unfold isSmall
  omega

/-! ### Status 8: IN MATHLIB (dark blue) -/
@[blueprint "thm:inmathlib" (mathlib := true)
  (title := "In Mathlib Example")
  (statement := /-- Already in Mathlib. \uses{thm:mathlibready} -/)
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
