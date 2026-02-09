/-
Statement attribute demonstration module for SBS-Test.
Shows attribute-based LaTeX authoring including:
1. Inline statement text (statement := /-- ... -/)
2. Above/below contextual paragraphs
3. Proof descriptions
4. Uses declarations

All LaTeX content is embedded directly in @[blueprint] attributes.
-/
import Dress
import Mathlib.Tactic

namespace SBSTest.StatementDemo

/-! ## Basic Statement Embedding

The `(statement := /-- ... -/)` syntax embeds the TeX statement
directly in the `@[blueprint]` attribute. This is the standard
authoring mode for all SBS blueprint projects.
-/

@[blueprint "attr_demo"
  (title := "Attribute Demo")
  (message := "Demonstrates basic attribute-based statement embedding")
  (above := /-- We begin with the simplest arithmetic identity on
  the natural numbers. The result is immediate from the definition
  of addition on $\mathbb{N}$. -/)
  (statement := /-- For all natural numbers $n$, we have $0 + n = n$.

  This is the classic left identity of addition on $\mathbb{N}$.

  \uses{} -/)
  (proof := /-- Direct application of the \texttt{omega} tactic, which
  decides linear arithmetic over the naturals. -/)
  (below := /-- With the additive identity established, we can proceed
  to commutativity and more complex properties of addition. -/)
  (latexEnv := "theorem")]
theorem attr_demo : ∀ n : Nat, 0 + n = n := by
  intro n
  omega

/-! ## Multi-Field Attributes

The following declarations show how multiple attribute fields work
together: `above` introduces context, `statement` gives the formal claim,
`proof` describes the proof strategy, and `below` provides follow-up.
-/

@[blueprint "delim_block_demo"
  (title := "Commutativity of Addition")
  (above := /-- Having established the left identity, we now show that
  addition on the naturals is commutative. This is a fundamental
  property used throughout the rest of the development. -/)
  (statement := /-- For all natural numbers $n$ and $m$, we have $n + m = m + n$. -/)
  (proof := /-- The commutativity of addition on $\mathbb{N}$ is
  resolved by the \texttt{omega} linear arithmetic decision procedure
  after introducing both universally quantified variables. -/)
  (below := /-- Commutativity, together with the identity lemma above,
  forms the basis for the abelian group structure of $(\mathbb{N}, +)$. -/)]
theorem delim_block_demo : ∀ n m : Nat, n + m = m + n := by
  intro n m
  omega

@[blueprint "delim_line_demo"
  (title := "The Answer")
  (statement := /-- A simple constant equal to $42$, demonstrating
  short statement text in a definition node. -/)
  (proof := /-- Defined as the literal value $42$. -/)]
def delim_line_demo : Nat := 42

/-! ## Logic Examples with Dependencies

These declarations form a small dependency chain demonstrating
how `uses` connects nodes in the graph.
-/

@[blueprint "attr_logic"
  (title := "Modus Ponens")
  (keyDeclaration := true)
  (above := /-- We now turn to propositional logic. The following result
  is the rule of modus ponens, one of the most fundamental inference
  rules. It connects the arithmetic results above to the logic chain below. -/)
  (statement := /-- If $P$ implies $Q$, and $P$ holds, then $Q$ holds.

  This is the rule of modus ponens, one of the fundamental
  inference rules of propositional logic. -/)
  (proof := /-- By direct function application: given the
  implication $P \to Q$ and a proof of $P$, apply the former
  to the latter to obtain $Q$. -/)
  (latexEnv := "theorem")]
theorem attr_logic : ∀ (P Q : Prop), (P → Q) → P → Q := by
  intro P Q hPQ hP
  exact hPQ hP

@[blueprint "delim_block_dne"
  (title := "Double Negation Intro")
  (statement := /-- For any proposition $P$, if $P$ holds then $\lnot\lnot P$ holds.
  That is, $P \to \lnot\lnot P$. -/)
  (proof := /-- Assume $P$ and $\lnot P$. Since $\lnot P$ is
  defined as $P \to \bot$, applying $\lnot P$ to the proof of $P$
  yields a contradiction. -/)
  (uses := ["attr_logic"])]
theorem delim_block_dne : ∀ (P : Prop), P → ¬¬P := by
  intro P hP hNotP
  exact hNotP hP

@[blueprint "delim_line_id"
  (title := "Identity Function")
  (statement := /-- The polymorphic identity function: for any type $\alpha$,
  maps each element to itself. -/)
  (proof := /-- Returns its argument unchanged; the definition
  is the identity map $a \mapsto a$. -/)]
def delim_line_id (α : Type) (a : α) : α := a

end SBSTest.StatementDemo
