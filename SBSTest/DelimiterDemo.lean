/-
Delimiter syntax demonstration module for SBS-Test.
Shows both authoring modes side by side:
1. Traditional attribute-based statements (statement := /-- ... -/)
2. Block delimiter TeX embedding (/-%%...%%-/)
3. Single-line delimiter TeX embedding (--%%...)

The delimiter comments are plain Lean comments that the SBS extractor
will parse to associate TeX blocks with @[blueprint] declarations.
-/
import Dress
import Mathlib.Tactic

namespace SBSTest.DelimiterDemo

/-! ## Mode 1: Traditional Attribute-Based Statement

The `(statement := /-- ... -/)` syntax embeds the TeX statement
directly in the `@[blueprint]` attribute. This is the original
authoring mode supported since the first release.
-/

@[blueprint "attr_demo"
  (title := "Attribute Demo")
  (message := "Traditional attribute-based statement embedding")
  (statement := /-- For all natural numbers $n$, we have $0 + n = n$.

  This is the classic left identity of addition on $\mathbb{N}$.

  \uses{} -/)
  (proof := /-- Direct application of the \texttt{omega} tactic, which
  decides linear arithmetic over the naturals. -/)
  (latexEnv := "theorem")]
theorem attr_demo : ∀ n : Nat, 0 + n = n := by
  intro n
  omega

/-! ## Mode 2: Block Delimiter TeX Embedding

The `/-%%...%%-/` syntax places the TeX in a block comment
immediately before the `@[blueprint]` declaration. The extractor
associates the TeX block with the next blueprint-annotated declaration.
-/

/-%%
For all natural numbers $n$ and $m$, we have $n + m = m + n$.
%%-/
@[blueprint "delim_block_demo"
  (title := "Block Delimiter Demo")
  (proof := /-- The commutativity of addition on $\mathbb{N}$ is
  resolved by the \texttt{omega} linear arithmetic decision procedure
  after introducing both universally quantified variables. -/)]
theorem delim_block_demo : ∀ n m : Nat, n + m = m + n := by
  intro n m
  omega

/-! ## Mode 3: Single-Line Delimiter TeX Embedding

The `--%%` prefix marks consecutive lines as TeX content.
Each line after the `--%%` prefix is concatenated to form
the full TeX block, associated with the next declaration.
-/

--%%A simple constant equal to $42$, demonstrating single-line
--%%delimiter syntax for short TeX blocks.
@[blueprint "delim_line_demo"
  (title := "Line Delimiter Demo")
  (proof := /-- Defined as the literal value $42$. -/)]
def delim_line_demo : Nat := 42

/-! ## Combined: Attribute + Delimiter Styles in One Module

The following declarations demonstrate that both styles can coexist
in the same file. This is the expected workflow during migration:
projects can adopt delimiters incrementally without rewriting
existing attribute-based statements.
-/

-- A second attribute-based example for comparison
@[blueprint "attr_logic"
  (title := "Modus Ponens")
  (keyDeclaration := true)
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

-- A second block delimiter example
/-%%
For any proposition $P$, if $P$ holds then $\lnot\lnot P$ holds.
That is, $P \to \lnot\lnot P$.
%%-/
@[blueprint "delim_block_dne"
  (title := "Double Negation Intro")
  (proof := /-- Assume $P$ and $\lnot P$. Since $\lnot P$ is
  defined as $P \to \bot$, applying $\lnot P$ to the proof of $P$
  yields a contradiction. -/)
  (uses := ["attr_logic"])]
theorem delim_block_dne : ∀ (P : Prop), P → ¬¬P := by
  intro P hP hNotP
  exact hNotP hP

-- A second single-line delimiter example
--%%The polymorphic identity function: for any type $\alpha$,
--%%maps each element to itself.
@[blueprint "delim_line_id"
  (title := "Identity Function")
  (proof := /-- Returns its argument unchanged; the definition
  is the identity map $a \mapsto a$. -/)]
def delim_line_id (α : Type) (a : α) : α := a

end SBSTest.DelimiterDemo
