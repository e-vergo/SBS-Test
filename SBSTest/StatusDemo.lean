/-
Status demonstration module for SBS-Test.
Tests all 6 status colors and graph check failures (connectivity + cycles).

## Status Colors (6):
1. notReady    - Sandy Brown (manual flag or no Lean code)
2. ready       - Light Sea Green (manual flag)
3. sorry       - Dark Red (derived: proof contains sorry)
4. proven      - Light Green (derived: complete proof)
5. fullyProven - Forest Green (auto-computed: all deps proven)
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

/-! ## Main Graph: 13 Connected Nodes

This section demonstrates the main connected component of the dependency graph.
Each node has a specific status to test the 6-color model.
-/

-- notReady: Manual flag
-- This is a foundational lemma that we're marking as not ready
-- It has multiple lines of comments to test comment highlighting
@[blueprint "foundation" (notReady := true)
  (title := "Foundation")
  (message := "Foundation lemma - manually marked not ready for formalization")
  (above := /-- This section introduces the foundational axiom for our test project.
  The result below connects the base axiom to the rest of the dependency graph. -/)
  (statement := /-- Foundation lemma, manually marked notReady.

  This represents a lemma that exists in the informal blueprint but
  is not yet ready to be formalized. Common reasons include:
  - Missing prerequisite lemmas
  - Unclear statement that needs clarification
  - Depends on unformalized concepts

  \uses{base_axiom} -/)
  (proof := /-- Immediate from the trivial tactic. -/)
  (below := /-- The foundation lemma is a prerequisite for all subsequent results
  in the formalization chain. See the ready-to-prove nodes next. -/)
  (uses := ["base_axiom"])]
theorem foundation : True := by
  -- Even though we have a proof, the manual notReady flag takes precedence
  -- This tests that manual status flags override auto-detection
  trivial  -- simple proof for testing purposes

/-! ## Ready Status Demonstrations

These nodes are marked as "ready" - meaning they're ready to be formalized
but haven't been completed yet. In practice, you'd use this for lemmas
where you have a clear proof strategy but haven't written the Lean code.
-/

-- Full-line comment before ready_to_prove
-- Testing multiple comment lines in sequence
-- Each should be highlighted in green italic
@[blueprint "ready_to_prove" (ready := true)
  (title := "Ready to Prove")
  (message := "Ready for formalization - proof strategy is clear")
  (statement := /-- A lemma that's ready to be formalized.

  The proof strategy is:
  1. Apply the foundation lemma
  2. Use basic logic

  \uses{foundation} -/)
  (proof := /-- Direct application of the \texttt{trivial} lemma. -/)
  (uses := ["foundation"])]
theorem ready_to_prove : True := by
  -- This proof exists but the ready flag is for demonstration
  exact trivial  -- inline comment on the tactic

@[blueprint "another_ready" (ready := true)
  (title := "Another Ready")
  (above := /-- This paragraph introduces the second ready-status lemma.
  It includes inline math $\alpha + \beta = \gamma$ to test LaTeX rendering
  in above blocks. The lemma below extends the ready-to-prove chain. -/)
  (statement := /-- Another lemma marked as ready.

  This tests that multiple ready nodes display correctly
  in the dependency graph and dashboard.

  \uses{ready_to_prove} -/)
  (proof := /-- The result is trivially true. -/)
  (below := /-- Having verified the above, we proceed to the sorry-status
  demonstrations which show how incomplete proofs propagate through
  the dependency graph. See the next section for details. -/)
  (uses := ["ready_to_prove"])]
theorem another_ready : True := by
  -- Comment inside the proof block
  -- Demonstrating comments in tactic mode
  trivial

/-! ## Sorry Status Demonstrations

Nodes with `sorry` in their proof automatically get the "sorry" status.
This is detected during elaboration and cannot be overridden by manual flags.
-/

-- This theorem intentionally has a sorry to demonstrate the sorry status
-- The sorry should make the node appear in dark red
@[blueprint "has_sorry"
  (title := "Has Sorry")
  (priorityItem := true)
  (blocked := "Waiting for upstream lemma from mathlib")
  (potentialIssue := "The sorry here is blocking downstream proofs")
  (statement := /-- This theorem has a sorry in its proof.

  The sorry indicates that the proof is incomplete.
  In a real project, you would:
  - Track why the sorry exists (blocked field)
  - Note any issues (potentialIssue field)
  - Mark as priorityItem if it's blocking progress

  \uses{another_ready} -/)
  (uses := ["another_ready"])]
theorem has_sorry : ∀ n : Nat, n + 0 = n := by
  -- We're using sorry here to demonstrate the sorry status
  -- In practice, this would be: intro n; rfl
  intro n
  -- The sorry below triggers the "sorry" status color
  sorry  -- TODO: replace with actual proof

@[blueprint "also_sorry"
  (title := "Also Sorry")
  (technicalDebt := "Need to prove this properly after has_sorry is done")
  (statement := /-- Another theorem with sorry.

  This demonstrates that sorry status propagates understanding
  through the dependency graph - nodes depending on sorry nodes
  cannot be fully proven until the sorry is resolved.

  \uses{has_sorry} -/)
  (uses := ["has_sorry"])]
theorem also_sorry : ∀ n : Nat, 0 + n = n := by
  -- Another sorry for testing
  intro n
  -- Comment before the sorry
  sorry  -- inline comment after sorry

/-! ## Proven Status Demonstrations

Nodes with complete proofs (no sorry) get the "proven" status.
However, if they depend on nodes with sorry, they won't be "fullyProven".
-/

-- A complete proof with no dependencies
-- This should show as "proven" (light green)
@[blueprint "proven_leaf"
  (title := "Proven Leaf")
  (message := "A proven leaf node - no dependencies, complete proof")
  (statement := /-- A proven leaf node with no dependencies.

  This is a simple theorem that we can prove completely.
  Since it has no dependencies, it will be marked as "fullyProven"
  automatically by the graph analysis. -/)
  (proof := /-- Introduce the proposition $P$ and its proof $h$, then return $h$ directly. This is the identity function on proofs. -/)]
theorem proven_leaf : ∀ (P : Prop), P → P := by
  -- This is a complete proof of the identity function on propositions
  -- Step 1: Introduce the proposition P
  intro P
  -- Step 2: Introduce the hypothesis h : P
  intro h
  -- Step 3: Return h as our proof of P
  exact h  -- QED: we've proven P → P

@[blueprint "proven_mid"
  (title := "Proven Mid")
  (message := "A proven node that depends on both sorry and proven nodes")
  (statement := /-- A proven node in the middle of the chain.

  This node has a complete proof but depends on:
  - also_sorry (which has a sorry)
  - proven_leaf (which is complete)

  Because of the sorry dependency, this cannot be "fullyProven".

  \uses{also_sorry, proven_leaf} -/)
  (proof := /-- Split the conjunction into two subgoals and discharge each by triviality. -/)
  (uses := ["also_sorry", "proven_leaf"])]
theorem proven_mid : True ∧ True := by
  -- A slightly more interesting proof using constructor
  constructor  -- splits into two goals
  · -- First goal: prove True
    trivial  -- inline: True is trivially true
  · -- Second goal: prove True
    -- Using exact instead of trivial for variety
    exact trivial

@[blueprint "proven_chain"
  (title := "Proven Chain")
  (statement := /-- A proven node continuing the chain.

  Demonstrates longer dependency chains and how status propagates.

  \uses{proven_mid} -/)
  (proof := /-- Prove the left disjunct of $\top \lor \bot$ directly, since $\top$ holds trivially. -/)
  (uses := ["proven_mid"])]
theorem proven_chain : True ∨ False := by
  -- We prove True ∨ False by proving the left disjunct
  -- This is a standard technique in constructive logic
  left  -- choose to prove the left side
  -- Now we just need to prove True
  trivial  -- easy!

/-! ## FullyProven Status Demonstrations

The "fullyProven" status is AUTO-COMPUTED by the graph analysis.
A node is fullyProven if:
1. It has a complete proof (no sorry)
2. ALL of its dependencies are also fullyProven

This creates a "proven chain" from leaves upward.
-/

-- This chain starts from proven_leaf (which has no deps)
-- So all nodes in this chain will be fullyProven
@[blueprint "fully_chain_1"
  (title := "Fully Chain 1")
  (keyDeclaration := true)
  (message := "First in the fully proven chain - starts from proven_leaf")
  (statement := /-- First node in the fully proven chain.

  This depends only on proven_leaf, which has no dependencies.
  Therefore, this entire dependency tree is complete and verified.

  \uses{proven_leaf} -/)
  (proof := /-- Apply the proven leaf theorem directly, which already establishes $\forall P,\; P \to P$. -/)
  (uses := ["proven_leaf"])]
theorem fully_chain_1 : ∀ (P : Prop), P → P := by
  -- We can use proven_leaf directly since it proves the same thing!
  exact proven_leaf  -- reusing the leaf theorem

@[blueprint "fully_chain_2"
  (title := "Fully Chain 2")
  (statement := /-- Second node in the fully proven chain.

  The dependency chain so far:
  proven_leaf → fully_chain_1 → fully_chain_2

  All nodes in this chain are completely verified.

  \uses{fully_chain_1} -/)
  (proof := /-- Introduce $P$, $Q$, and a proof of $P$. Discard the hypothesis of $Q$ and return the proof of $P$. This is the weakening principle. -/)
  (uses := ["fully_chain_1"])]
theorem fully_chain_2 : ∀ (P Q : Prop), P → (Q → P) := by
  -- A more interesting proof showing weakening
  intro P Q  -- introduce both propositions
  intro hP   -- assume P
  intro _hQ  -- assume Q (but we won't use it)
  -- We need to prove P, and we have hP : P
  exact hP  -- done!

@[blueprint "fully_chain_3"
  (title := "Fully Chain 3")
  (statement := /-- Third node in the fully proven chain.

  The complete verified chain:
  proven_leaf → fully_chain_1 → fully_chain_2 → fully_chain_3

  All ancestors are proven, so this is fullyProven.

  \uses{fully_chain_2} -/)
  (proof := /-- Given a proof $h$ of $P$, apply the left injection into $P \lor P$. -/)
  (uses := ["fully_chain_2"])]
theorem fully_chain_3 : ∀ (P : Prop), P → P ∨ P := by
  -- Proof that P implies P ∨ P
  intro P hP  -- introduce P and hypothesis hP : P
  -- We can prove P ∨ P by proving either side
  left   -- choose left disjunct
  exact hP  -- use our hypothesis

/-! ## MathlibReady Status Demonstration

The "mathlibReady" status is a MANUAL flag indicating that a theorem
is ready for submission to mathlib (or has been submitted).
-/

@[blueprint "mathlib_theorem" (mathlibReady := true)
  (title := "Mathlib Ready Theorem")
  (keyDeclaration := true)
  (message := "Ready for mathlib submission - clean proof, good docs")
  (misc := "PR #12345 submitted")
  (statement := /-- A theorem ready for mathlib submission.

  This theorem meets mathlib standards:
  - Clear mathematical statement
  - Clean, idiomatic proof
  - Good documentation
  - No unnecessary dependencies

  \uses{fully_chain_1} -/)
  (proof := /-- Chain the two hypotheses $P \to Q$ and $Q \to R$ by function composition to obtain $P \to R$. -/)
  (uses := ["fully_chain_1"])]
theorem mathlib_theorem : ∀ (P Q R : Prop), (P → Q) → (Q → R) → (P → R) := by
  -- Proof of transitivity of implication
  -- This is a fundamental theorem in propositional logic
  intro P Q R  -- introduce the three propositions
  intro hPQ    -- hypothesis: P → Q
  intro hQR    -- hypothesis: Q → R
  intro hP     -- hypothesis: P (we need to prove R)
  -- Chain the implications: P → Q → R
  apply hQR    -- suffices to prove Q
  apply hPQ    -- suffices to prove P
  exact hP     -- we have P

/-! ## Disconnected Cycle: 2 Nodes

These nodes form a cycle (A → B → A) and are NOT connected to the main graph.
This tests both cycle detection and disconnected component detection.

The graph validator should report:
1. A disconnected component containing {cycle_a, cycle_b}
2. A cycle: cycle_a → cycle_b → cycle_a
-/

-- Comment explaining the cycle
-- These two nodes reference each other, creating a dependency cycle
-- Cycles are usually a sign of a logical error in the blueprint
@[blueprint "cycle_a"
  (title := "Cycle A")
  (potentialIssue := "Part of a cyclic dependency - needs restructuring")
  (message := "This node is in a cycle with cycle_b")
  (statement := /-- Part of a cycle (disconnected from main graph).

  This demonstrates what happens when you have circular dependencies:
  - cycle_a depends on cycle_b
  - cycle_b depends on cycle_a

  This is usually an error that needs to be fixed by:
  1. Breaking one of the dependencies
  2. Restructuring the lemmas
  3. Finding a common base lemma

  \uses{cycle_b} -/)
  (proof := /-- Split the biconditional into both directions and discharge each by the identity. -/)
  (uses := ["cycle_b"])]
theorem cycle_a : True ↔ True := by
  -- Proof of True ↔ True (trivial but demonstrates the cycle issue)
  constructor  -- split into two directions
  · intro h; exact h  -- forward direction
  · intro h; exact h  -- backward direction

@[blueprint "cycle_b"
  (title := "Cycle B")
  (potentialIssue := "Part of a cyclic dependency - needs restructuring")
  (message := "This node is in a cycle with cycle_a")
  (statement := /-- Part of a cycle (disconnected from main graph).

  The other half of the cycle_a ↔ cycle_b dependency cycle.

  \uses{cycle_a} -/)
  (proof := /-- Both directions of the biconditional follow immediately by assumption. -/)
  (uses := ["cycle_a"])]
theorem cycle_b : True ↔ True := by
  -- Same proof structure as cycle_a
  -- In a real project, you'd break this cycle
  constructor
  · intro h
    -- Using a slightly different proof style
    assumption  -- uses h directly
  · intro h
    assumption

-- Final comments in the file
-- Testing that end-of-file comments work correctly
-- with multiple lines and various content

end SBSTest.StatusDemo
