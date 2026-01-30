/-
Status demonstration module for SBS-Test.
Tests all 6 status colors and graph check failures (connectivity + cycles).

## Status Colors (6):
1. notReady    - Sandy Brown (manual flag or no Lean code)
2. ready       - Light Sea Green (manual flag)
3. sorry       - Dark Red (derived: proof contains sorry)
4. proven      - Light Green (derived: complete proof)
5. fullyProven - Forest Green (manual flag, all deps proven)
6. mathlibReady- Light Blue (manual flag)

## Graph Structure:
- Main component: 13 connected nodes
- Disconnected cycle: 2 nodes (cycle_a <-> cycle_b)
- Total: 15 nodes

## Validation Tests:
- Disconnected component detection (cycle is isolated)
- Cycle detection (cycle_a and cycle_b)
-/
import Dress
import Mathlib.Tactic

namespace SBSTest.StatusDemo

/-! ## Main Graph: 13 Connected Nodes -/

-- notReady: base_axiom has no Lean code (LaTeX only)
-- This declaration is for foundation only

-- notReady: Manual flag
@[blueprint "foundation" (notReady := true)
  (title := "Foundation")
  (message := "Foundation lemma - manually marked not ready")
  (statement := /-- Foundation lemma, manually marked notReady. \uses{base_axiom} -/)
  (uses := ["base_axiom"])]
theorem foundation : True := trivial

-- ready: Manual flags
@[blueprint "ready_to_prove" (ready := true)
  (title := "Ready to Prove")
  (message := "Ready for formalization")
  (statement := /-- Ready to be formalized. \uses{foundation} -/)
  (uses := ["foundation"])]
theorem ready_to_prove : True := trivial

@[blueprint "another_ready" (ready := true)
  (title := "Another Ready")
  (statement := /-- Another lemma ready to prove. \uses{ready_to_prove} -/)
  (uses := ["ready_to_prove"])]
theorem another_ready : True := trivial

-- sorry: Has sorry in proof
@[blueprint "has_sorry"
  (title := "Has Sorry")
  (priorityItem := true)
  (blocked := "Waiting for upstream lemma")
  (statement := /-- This theorem has a sorry in its proof. \uses{another_ready} -/)
  (uses := ["another_ready"])]
theorem has_sorry : 1 = 1 := by sorry

@[blueprint "also_sorry"
  (title := "Also Sorry")
  (statement := /-- Another theorem with sorry. \uses{has_sorry} -/)
  (uses := ["has_sorry"])]
theorem also_sorry : 2 = 2 := by sorry

-- proven: Complete proofs
@[blueprint "proven_leaf"
  (title := "Proven Leaf")
  (keyDeclaration := true)
  (message := "A proven leaf node - no dependencies")
  (statement := /-- A proven leaf node with no dependencies. -/)]
theorem proven_leaf : True := trivial

@[blueprint "proven_mid"
  (title := "Proven Mid")
  (statement := /-- A proven node in the middle of the chain. \uses{also_sorry, proven_leaf} -/)
  (uses := ["also_sorry", "proven_leaf"])]
theorem proven_mid : True := trivial

@[blueprint "proven_chain"
  (title := "Proven Chain")
  (statement := /-- A proven node continuing the chain. \uses{proven_mid} -/)
  (uses := ["proven_mid"])]
theorem proven_chain : True := trivial

-- fullyProven: Manual flag (all ancestors should be proven)
-- These use proven_leaf so the dependency chain is: proven_leaf -> fully_chain_1 -> fully_chain_2 -> fully_chain_3
@[blueprint "fully_chain_1" (fullyProven := true)
  (title := "Fully Chain 1")
  (keyDeclaration := true)
  (message := "First in the fully proven chain")
  (statement := /-- First node in the fully proven chain. \uses{proven_leaf} -/)
  (uses := ["proven_leaf"])]
theorem fully_chain_1 : True := proven_leaf

@[blueprint "fully_chain_2" (fullyProven := true)
  (title := "Fully Chain 2")
  (statement := /-- Second node in the fully proven chain. \uses{fully_chain_1} -/)
  (uses := ["fully_chain_1"])]
theorem fully_chain_2 : True := fully_chain_1

@[blueprint "fully_chain_3" (fullyProven := true)
  (title := "Fully Chain 3")
  (statement := /-- Third node in the fully proven chain. \uses{fully_chain_2} -/)
  (uses := ["fully_chain_2"])]
theorem fully_chain_3 : True := fully_chain_2

-- mathlibReady: Manual flag
@[blueprint "mathlib_theorem" (mathlibReady := true)
  (title := "Mathlib Theorem")
  (keyDeclaration := true)
  (message := "Ready for mathlib submission")
  (statement := /-- A theorem ready for mathlib. \uses{fully_chain_1} -/)
  (uses := ["fully_chain_1"])]
theorem mathlib_theorem : True := trivial

/-! ## Disconnected Cycle: 2 Nodes

These nodes form a cycle (A -> B -> A) and are NOT connected to the main graph.
This tests both cycle detection and disconnected component detection.
-/

@[blueprint "cycle_a"
  (title := "Cycle A")
  (potentialIssue := "Part of a cyclic dependency - needs restructuring")
  (statement := /-- Part of a cycle (disconnected from main graph). \uses{cycle_b} -/)
  (uses := ["cycle_b"])]
theorem cycle_a : True := trivial

@[blueprint "cycle_b"
  (title := "Cycle B")
  (potentialIssue := "Part of a cyclic dependency - needs restructuring")
  (statement := /-- Part of a cycle (disconnected from main graph). \uses{cycle_a} -/)
  (uses := ["cycle_a"])]
theorem cycle_b : True := trivial

end SBSTest.StatusDemo
