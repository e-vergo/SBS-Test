/-
SBS-Test: Core declarations for the Side-by-Side Blueprint test project.

## DAG Structure (20 Lean declarations + 1 TeX-only node):

Branch A (Arithmetic -- contains sorry):
  base_axiom (TeX-only) → foundation → nat_identity → add_zero (sorry)
    → add_comm (sorry) → add_assoc (proven, blocked by sorry ancestors)

Branch B (Set theory):
  foundation → set_basics → choice_axiom (Lean axiom) → elem_self
    → subset_refl

Branch C (Logic -- fully provable chain):
  proven_leaf → imp_trans → weakening → contrapositive
  contrapositive + weakening → disjunction_intro (diamond)

Merging:
  add_assoc + subset_refl → core_theorem (diamond merge)
  core_theorem + weakening → synthesis (cross-branch merge)
  synthesis → advanced_composition
  synthesis → main_result (keyDecl)
  weakening → mathlib_ready (mathlibReady)

## Status Coverage (7-status model):
  notReady:     foundation (explicit flag)
  wip:          nat_identity, set_basics (manual flag)
  sorry:        add_zero, add_comm (derived from sorry in proof)
  proven:       elem_self, subset_refl, add_assoc, core_theorem,
                synthesis, advanced_composition, main_result
                (derived — has Lean proof, no sorry, but unclean ancestors)
  fullyProven:  proven_leaf, imp_trans, weakening, contrapositive,
                disjunction_intro (auto-computed, all ancestors clean)
  axiom:        choice_axiom (auto-detected from Lean `axiom` keyword)
  mathlibReady: mathlib_ready (manual flag)
-/
import Dress
import Mathlib.Tactic

namespace SBSTest.StatusDemo

/-! ## Branch A: Arithmetic (contains sorry)

This branch demonstrates sorry propagation through a dependency chain.
Even when downstream nodes have complete proofs, the sorry in an
ancestor prevents fullyProven status.
-/

-- foundation: manually notReady, depends on TeX-only base_axiom
@[blueprint "foundation" (notReady := true)
  (title := "Foundation")
  (message := "Foundation lemma — manually marked not ready for formalization")
  (above := /-- This section introduces the foundational result connecting
  the base axiom to the rest of the dependency graph. -/)
  (statement := /-- Foundation lemma, manually marked notReady.

  This represents a result that exists in the informal blueprint but
  is not yet ready to be formalized. The manual \texttt{notReady} flag
  overrides the auto-detected status.

  \uses{base_axiom} -/)
  (proof := /-- Immediate from the trivial tactic. -/)
  (below := /-- The foundation lemma is a prerequisite for both the
  arithmetic chain (Branch A) and the set theory chain (Branch B). -/)
  (uses := ["base_axiom"])]
theorem foundation : True := by trivial

-- nat_identity: wip status, depends on foundation
@[blueprint "nat_identity" (wip := true)
  (title := "Natural Number Identity")
  (message := "Work in progress — proof strategy is clear")
  (statement := /-- The identity element for natural number addition.

  For all $n \in \mathbb{N}$, we have $n + 0 = n$.
  This is ready to be formalized but awaits upstream work.

  \uses{foundation} -/)
  (proof := /-- By reflexivity of natural number addition with zero. -/)
  (uses := ["foundation"])]
theorem nat_identity : ∀ n : Nat, n + 0 = n := by
  intro n; rfl

-- add_zero: sorry status, depends on nat_identity
@[blueprint "add_zero"
  (title := "Addition with Zero")
  (priorityItem := true)
  (blocked := "Waiting for upstream infrastructure from mathlib")
  (potentialIssue := "The sorry here blocks all downstream proofs in Branch A")
  (statement := /-- Left identity of addition: $0 + n = n$ for all $n \in \mathbb{N}$.

  \uses{nat_identity} -/)
  (proof := /-- Proof by induction on $n$. The base case is immediate;
  the inductive step uses the successor property of addition. -/)
  (uses := ["nat_identity"])]
theorem add_zero : ∀ n : Nat, 0 + n = n := by
  intro n
  sorry

-- add_comm: sorry status, depends on add_zero
@[blueprint "add_comm"
  (title := "Commutativity of Addition")
  (technicalDebt := "Need to prove this properly after add_zero is resolved")
  (statement := /-- Commutativity of addition: $m + n = n + m$ for all $m, n \in \mathbb{N}$.

  \uses{add_zero} -/)
  (proof := /-- By induction on $m$, using the left identity and
  the commutativity of the successor operation. -/)
  (uses := ["add_zero"])]
theorem add_comm : ∀ m n : Nat, m + n = n + m := by
  intro m n
  sorry

-- add_assoc: proven (complete proof), depends on add_comm
-- Not fullyProven because add_comm has sorry
@[blueprint "add_assoc"
  (title := "Associativity of Addition")
  (message := "Proven but not fully verified — sorry in ancestry")
  (statement := /-- Associativity of addition: $(a + b) + c = a + (b + c)$.

  This node has a complete proof but cannot be \texttt{fullyProven}
  because its ancestor \texttt{add\_comm} contains a sorry.

  \uses{add_comm} -/)
  (proof := /-- We prove a simpler propositional statement that
  suffices, using the trivial tactic. -/)
  (uses := ["add_comm"])]
theorem add_assoc : True := by trivial

/-! ## Branch B: Set Theory

This branch tests the Lean `axiom` keyword and demonstrates
how axioms integrate into the dependency graph.
-/

-- set_basics: wip status, depends on foundation
@[blueprint "set_basics" (wip := true)
  (title := "Set Theory Basics")
  (misc := "Placeholder for set-theoretic foundations")
  (statement := /-- Basic set membership properties.

  For a set $S$ and element $x$, we establish the fundamental
  properties of membership and containment.

  \uses{foundation} -/)
  (proof := /-- Trivially true as a propositional placeholder. -/)
  (uses := ["foundation"])]
theorem set_basics : True := by trivial

-- choice_axiom: Lean `axiom` keyword, depends on set_basics
@[blueprint "choice_axiom"
  (title := "Choice Axiom")
  (message := "Lean axiom declaration — no proof required")
  (statement := /-- A choice principle: for any nonempty type $\alpha$,
  there exists an element of $\alpha$.

  This is declared as a Lean \texttt{axiom}, which Dress auto-detects
  via \texttt{ConstantInfo.axiomInfo}.

  \uses{set_basics} -/)
  (uses := ["set_basics"])]
axiom choice_axiom : ∀ (α : Type) [Inhabited α], α

-- elem_self: proven, depends on choice_axiom
@[blueprint "elem_self"
  (title := "Element Self-Membership")
  (statement := /-- An element belongs to its singleton set.

  For any proposition $P$, the proof $P \to P$ witnesses
  self-containment in the logical sense.

  \uses{choice_axiom} -/)
  (proof := /-- By the identity function on proofs:
  introduce $P$ and its proof $h$, then return $h$ directly. -/)
  (uses := ["choice_axiom"])]
theorem elem_self : ∀ (P : Prop), P → P := by
  intro P h; exact h

-- subset_refl: proven, depends on elem_self
@[blueprint "subset_refl"
  (title := "Subset Reflexivity")
  (statement := /-- Every set is a subset of itself: $A \subseteq A$.

  Represented propositionally as $P \land P \to P$.

  \uses{elem_self} -/)
  (proof := /-- Extract the left component of the conjunction. -/)
  (uses := ["elem_self"])]
theorem subset_refl : ∀ (P : Prop), P ∧ P → P := by
  intro P ⟨h, _⟩; exact h

/-! ## Branch C: Logic (Fully Provable Chain)

This branch has NO sorry and NO manual status overrides in its ancestry.
All nodes auto-compute to fullyProven via the graph analysis.
-/

-- proven_leaf: no dependencies, complete proof → auto fullyProven
@[blueprint "proven_leaf"
  (title := "Proven Leaf")
  (message := "Leaf node with no dependencies — auto fullyProven")
  (statement := /-- The identity principle: every proposition implies itself.

  Since this node has no dependencies and a complete proof,
  the graph analysis marks it as \texttt{fullyProven} automatically. -/)
  (proof := /-- Introduce the proposition $P$ and its proof $h$,
  then return $h$ directly. This is the identity function on proofs. -/)]
theorem proven_leaf : ∀ (P : Prop), P → P := by
  intro P h; exact h

-- imp_trans: depends only on proven_leaf → auto fullyProven
@[blueprint "imp_trans"
  (title := "Transitivity of Implication")
  (statement := /-- Transitivity: if $P \to Q$ and $Q \to R$ then $P \to R$.

  \uses{proven_leaf} -/)
  (proof := /-- Chain the two implications by function composition. -/)
  (uses := ["proven_leaf"])]
theorem imp_trans : ∀ (P Q R : Prop), (P → Q) → (Q → R) → (P → R) := by
  intro P Q R hPQ hQR hP
  exact hQR (hPQ hP)

-- weakening: depends only on imp_trans → auto fullyProven
@[blueprint "weakening"
  (title := "Weakening Principle")
  (statement := /-- Weakening: from $P$ we can derive $Q \to P$ for any $Q$.

  \uses{imp_trans} -/)
  (proof := /-- Introduce $P$, $Q$, and a proof of $P$.
  Discard the hypothesis of $Q$ and return the proof of $P$. -/)
  (uses := ["imp_trans"])]
theorem weakening : ∀ (P Q : Prop), P → (Q → P) := by
  intro P Q hP _hQ; exact hP

-- contrapositive: depends only on imp_trans → auto fullyProven
@[blueprint "contrapositive"
  (title := "Contrapositive")
  (statement := /-- The contrapositive: $(P \to Q) \to (\neg Q \to \neg P)$.

  \uses{imp_trans} -/)
  (proof := /-- Given $h : P \to Q$ and $hnq : \neg Q$, assume $hp : P$.
  Then $h(hp) : Q$ contradicts $hnq$. -/)
  (uses := ["imp_trans"])]
theorem contrapositive : ∀ (P Q : Prop), (P → Q) → (¬Q → ¬P) := by
  intro P Q h hnq hp
  exact hnq (h hp)

-- disjunction_intro: depends on contrapositive + weakening → diamond → auto fullyProven
@[blueprint "disjunction_intro"
  (title := "Disjunction Introduction")
  (statement := /-- Left disjunction introduction: $P \to P \lor Q$.

  This node demonstrates a diamond pattern in the DAG:
  both \texttt{contrapositive} and \texttt{weakening} depend on
  \texttt{imp\_trans}, and this node depends on both.

  \uses{contrapositive, weakening} -/)
  (proof := /-- Apply the left injection into the disjunction. -/)
  (uses := ["contrapositive", "weakening"])]
theorem disjunction_intro : ∀ (P Q : Prop), P → P ∨ Q := by
  intro P _Q hP; exact Or.inl hP

/-! ## Merging: Cross-Branch Dependencies

These nodes merge the three branches, creating a rich DAG structure
with diamond patterns and cross-branch dependencies.
-/

-- core_theorem: diamond merge of add_assoc (Branch A) + subset_refl (Branch B)
@[blueprint "core_theorem"
  (title := "Core Theorem")
  (keyDeclaration := true)
  (message := "Central theorem merging arithmetic and set theory branches")
  (statement := /-- The core theorem merging Branches A and B.

  This creates a diamond pattern: both \texttt{add\_assoc} and
  \texttt{subset\_refl} trace back to \texttt{foundation}, and
  this node depends on both.

  \uses{add_assoc, subset_refl} -/)
  (proof := /-- Split the conjunction and prove each component trivially. -/)
  (uses := ["add_assoc", "subset_refl"])]
theorem core_theorem : True ∧ True := by
  exact ⟨trivial, trivial⟩

-- synthesis: merges core_theorem (A+B) with weakening (C)
@[blueprint "synthesis"
  (title := "Synthesis")
  (statement := /-- Synthesis of all three branches.

  Merges the core theorem (Branches A+B) with the weakening principle
  (Branch C), connecting all parts of the dependency graph.

  \uses{core_theorem, weakening} -/)
  (proof := /-- The disjunction $\top \lor \bot$ holds by left injection. -/)
  (uses := ["core_theorem", "weakening"])]
theorem synthesis : True ∨ False := by
  exact Or.inl trivial

-- advanced_composition: extends synthesis
@[blueprint "advanced_composition"
  (title := "Advanced Composition")
  (technicalDebt := "Could be generalized to arbitrary function chains")
  (statement := /-- An advanced composition extending the synthesis.

  \uses{synthesis} -/)
  (proof := /-- Direct consequence of the synthesis result. -/)
  (uses := ["synthesis"])]
theorem advanced_composition : True := by trivial

-- main_result: the main result of the project
@[blueprint "main_result"
  (title := "Main Result")
  (keyDeclaration := true)
  (message := "The main result — proven but not fullyProven due to sorry ancestors")
  (statement := /-- The main result of the SBS-Test project.

  This theorem depends transitively on both sorry-containing nodes
  (via synthesis $\to$ core\_theorem $\to$ add\_assoc $\to$ add\_comm)
  and the fully proven chain (via synthesis $\to$ weakening).

  \uses{synthesis} -/)
  (proof := /-- Follows directly from synthesis. -/)
  (uses := ["synthesis"])]
theorem main_result : True := by trivial

-- mathlib_ready: on the clean chain, mathlibReady status
@[blueprint "mathlib_ready" (mathlibReady := true)
  (title := "Mathlib-Ready Theorem")
  (keyDeclaration := true)
  (message := "Ready for mathlib submission — clean proof, good docs")
  (misc := "PR draft in preparation")
  (statement := /-- A theorem ready for mathlib submission.

  This node depends only on the fully proven chain (Branch C),
  so its dependency tree is entirely verified.

  \uses{weakening} -/)
  (proof := /-- By universal instantiation: introduce $P$, then
  prove $P \lor P$ from any proof of $P$ via left injection. -/)
  (uses := ["weakening"])]
theorem mathlib_ready : ∀ (P : Prop), P → P ∨ P := by
  intro P hP; exact Or.inl hP

end SBSTest.StatusDemo
