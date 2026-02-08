/-
Bracket demonstration module for rainbow bracket highlighting.

This module showcases various bracket nesting patterns to test
the rainbow bracket highlighting feature in the Side-by-Side Blueprint.

## Bracket Types:
- Parentheses: ()
- Square brackets: []
- Curly braces: {}

Each bracket depth level gets a different color (cycling through 6 colors).
After 6 levels, colors wrap around (level 7 = color 1, etc.).

## Comment Types Tested:
- Full-line comments (-- on their own line)
- Inline comments (-- at end of code line)
- Multi-line doc comments (/-- ... -/)
-/
import Dress
import Mathlib.Tactic

namespace SBSTest.BracketDemo

/-! ## Basic Bracket Nesting

These examples show simple bracket patterns with various nesting depths.
-/

-- This is a full-line comment before the theorem
-- It spans multiple lines to test comment highlighting
-- Each line should be highlighted in green
@[blueprint "bracket:nested"
  (title := "Nested Parentheses")
  (message := "Demonstrates rainbow bracket highlighting with 3 levels")
  (statement := /-- Associativity of addition with nested parentheses.

  This theorem demonstrates the associativity property:
  $$(a + (b + c)) = ((a + b) + c)$$

  The proof uses the `omega` tactic which handles linear arithmetic. -/)
  (proof := /-- Discharged in one step by the \texttt{omega} tactic, which decides linear arithmetic over the naturals. -/)]
theorem nested_parens (a b c : Nat) : (a + (b + c)) = ((a + b) + c) := by
  -- This comment explains the proof strategy
  -- We use omega because it handles linear arithmetic over naturals
  omega  -- inline comment: omega solves this automatically

-- Another full-line comment between declarations
-- Testing that comments work correctly between @[blueprint] items
@[blueprint "bracket:function"
  (title := "Mixed Brackets")
  (statement := /-- A function with mixed bracket types.

  This definition uses:
  - Parentheses for function application
  - Square brackets implicitly in List operations
  - Lambda expressions with arrow types -/)
  (proof := /-- Constructed by mapping a lambda that applies $f$ twice to each element of the input list. -/)]
def bracket_function (f : Nat → Nat) (xs : List Nat) : List Nat :=
  -- Map applies f twice to each element
  -- This creates nested function applications
  xs.map (fun x =>
    -- Inner comment inside lambda
    f (f x))  -- nested calls: f(f(x))

/-! ## Type-Level Brackets

Implicit type parameters use curly braces `{α : Type}`.
These should be colored differently from parentheses.
-/

@[blueprint "bracket:types"
  (title := "Type Brackets")
  (message := "Shows implicit type brackets with curly braces")
  (statement := /-- A theorem with implicit type parameters.

  The `{α : Type}` syntax introduces an implicit type parameter.
  Lean will infer the actual type from context. -/)
  (proof := /-- The hypothesis $h : x \in s$ is exactly the goal, so we apply it directly. -/)]
theorem type_example {α : Type} (s : Set α) (x : α) (h : x ∈ s) : x ∈ s := by
  -- The proof is trivial since h is exactly what we need
  exact h  -- h : x ∈ s is our hypothesis

/-! ## Deep Nesting Test (7+ levels)

This section tests that bracket colors wrap around correctly.
After 6 colors, level 7 should use color 1 again.

Color mapping (1-indexed):
- Level 1: Color 1 (magenta)
- Level 2: Color 2 (purple)
- Level 3: Color 3 (cyan)
- Level 4: Color 4 (blue)
- Level 5: Color 5 (green)
- Level 6: Color 6 (red)
- Level 7: Color 1 (magenta again - wrap around!)
- Level 8: Color 2 (purple again)
-/

-- Full line comment before the deep nesting example
-- This tests that comments don't interfere with bracket counting
@[blueprint "bracket:deep"
  (title := "Deep Nesting (8 Levels)")
  (message := "Tests bracket color wrap-around after 6 colors")
  (statement := /-- Definition with 8 levels of nested parentheses.

  This is specifically designed to test that bracket colors
  wrap around correctly after the 6th level:
  - Levels 1-6: Each gets a unique color
  - Level 7: Wraps to color 1
  - Level 8: Wraps to color 2 -/)
  (proof := /-- Defined as a single arithmetic expression with eight nested parenthesised additions, evaluated at compile time. -/)]
def deep_nesting : Nat :=
  -- Level:  1 2 3 4 5 6 7 8
  --         ( ( ( ( ( ( ( (
  ((((((((1 + 2) + 3) + 4) + 5) + 6) + 7) + 8) + 9)
  -- The innermost pair is level 8, should be color 2

-- Comment explaining the mixed deep nesting below
-- Uses all three bracket types at various depths
@[blueprint "bracket:mixed_deep"
  (title := "Mixed Deep Nesting")
  (statement := /-- Complex expression mixing all bracket types at depth 7+.

  This combines:
  - Curly braces for implicit arguments
  - Parentheses for grouping
  - Square brackets for list literals -/)
  (proof := /-- Constructed as a literal list of \texttt{Option (List $\alpha$)} values, mixing \texttt{some} and \texttt{none} with nested list and coercion expressions. -/)]
def mixed_deep_nesting {α : Type} [Inhabited α] : List (Option (List α)) :=
  -- Comment inside the definition
  -- Each line below has different nesting patterns
  [some [default],  -- level 3: [ ( [ ... ] ) ]
   some (([default] : List α)),  -- level 4: ( ( [ ] ) )
   none,
   some (((([default] : List α))))]  -- level 6!

/-! ## Complex Expression Tests

These test realistic code patterns with mixed brackets and comments.
-/

@[blueprint "bracket:complex"
  (title := "All Bracket Types")
  (keyDeclaration := true)
  (message := "Combines all three bracket types in realistic code")
  (statement := /-- A complex filtering function using all bracket types.

  This definition demonstrates:
  - Implicit type parameter `{α : Type}`
  - Explicit parameters in parentheses
  - List operations with square brackets
  - Conditional expressions -/)
  (proof := /-- Case-splits on whether the input list is empty: returns \texttt{none} for the empty list, and \texttt{some} of the filtered sublist otherwise. -/)]
def all_brackets {α : Type} (xs : List α) (p : α → Bool) : Option (List α) :=
  -- First check if the list is empty
  if xs.isEmpty then
    -- Return none for empty input
    none  -- inline: nothing to filter
  else
    -- Filter and wrap in Some
    some (xs.filter p)  -- filter preserves order

-- Full line comment testing special characters
-- Testing: dashes -- inside -- comments -- work
-- Testing: brackets in comments (like this) [and this] {and this}
-- The above brackets should NOT be rainbow colored!
@[blueprint "bracket:realistic"
  (title := "Realistic Function")
  (message := "A more realistic function with comments")
  (statement := /-- x^2 +2x + 3-/)
  (proof := /-- Pattern-matches on the list: the empty list returns $0$, a singleton applies $f$, and the cons case recursively folds via $g$. -/)]
def realistic_func (f : Nat → Nat) (g : Nat → Nat → Nat) (xs : List Nat) : Nat :=
  -- Handle empty list case
  match xs with
  | [] => 0  -- base case: empty list returns 0
  | [x] => f x  -- single element: just apply f
  | x :: rest =>
    -- Recursive case: apply f to head, combine with recursive result
    -- This creates nested applications of g
    g (f x) (realistic_func f g rest)  -- recursive call

/-! ## Extreme Nesting Test

This pushes the bracket nesting to 10 levels to thoroughly test wrap-around.
-/

@[blueprint "bracket:extreme"
  (title := "Extreme Nesting (10 Levels)")
  (priorityItem := true)
  (blocked := "Intentionally complex for testing")
  (statement := /-- An extremely nested expression for stress testing.

  10 levels of nesting tests two full color cycles plus 4:
  - Levels 1-6: Colors 1-6
  - Levels 7-10: Colors 1-4 (wrap around)

  This ensures the modulo arithmetic in `wrapBracketsWithDepth` works correctly. -/)
  (proof := /-- Defined as a lambda taking two naturals and returning a single deeply nested arithmetic expression combining addition, multiplication, subtraction, division, and modulo. -/)]
def extreme_nesting : Nat → Nat → Nat := fun a b =>
  -- 10 levels deep with mixed bracket types
  -- Count: { ( ( ( [ ( ( ( ( ( ... ) ) ) ) ) ] ) ) ) }
  (((((((((a + b) * 2) - 1) + 3) / 2) % 10) + a) * b) + 1)

-- Final comment block
-- This tests that comments at the end of a file work correctly
-- Multiple lines of comments here
-- With various content types:
--   - Indented text
--   - Special chars: → ← ↔ ∀ ∃ ∈ ∉ ⊆ ⊇
--   - Code-like: if x then y else z
-- End of comment block

/-! ## Tactic-Mode Proofs

These theorems demonstrate multi-step tactic proofs with `by` blocks.
They test the tactic state toggle feature in the Side-by-Side display.
-/

@[blueprint "bracket:nat_add_comm_tactic"
  (title := "Nat.add commutativity (tactic proof)")
  (message := "Multi-step induction proof demonstrating tactic state display")
  (statement := /-- Commutativity of natural number addition, proven by induction.

  This proof uses structured tactics with `induction` and `omega`:
  - Base case: `n + 0 = 0 + n` solved by omega
  - Inductive case: Uses omega with the induction hypothesis -/)
  (proof := /-- By induction on $m$. Both the base case ($m = 0$) and the inductive step ($m = k + 1$) are resolved by the \texttt{omega} tactic using linear arithmetic. -/)]
theorem nat_add_comm_tactic (n m : Nat) : n + m = m + n := by
  induction m with
  | zero => omega
  | succ m ih => omega

@[blueprint "bracket:list_length_append_tactic"
  (title := "List append length (tactic proof)")
  (message := "Induction on lists with simp and arithmetic")
  (statement := /-- The length of appended lists equals the sum of their lengths.

  This proof demonstrates:
  - Induction on the list structure
  - Using `simp` to simplify list operations
  - Using `omega` for arithmetic -/)
  (proof := /-- By structural induction on the first list. The nil case simplifies directly. The cons case unfolds the append and length definitions with \texttt{simp}, then closes the arithmetic goal with \texttt{omega}. -/)]
theorem list_length_append_tactic {α : Type} (xs ys : List α) :
    (xs ++ ys).length = xs.length + ys.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.cons_append, List.length_cons]
    omega

end SBSTest.BracketDemo
