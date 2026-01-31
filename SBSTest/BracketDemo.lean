/-
Bracket demonstration module for rainbow bracket highlighting.

This module showcases various bracket nesting patterns to test
the rainbow bracket highlighting feature in the Side-by-Side Blueprint.

## Bracket Types:
- Parentheses: ()
- Square brackets: []
- Curly braces: {}

Each bracket depth level gets a different color (cycling through 6 colors).
-/
import Dress
import Mathlib.Tactic

namespace SBSTest.BracketDemo

-- Nested parentheses demonstration
-- Shows 3 levels of nested parentheses with different colors
@[blueprint "bracket:nested"
  (title := "Nested Parentheses")
  (message := "Demonstrates rainbow bracket highlighting")
  (statement := /-- Associativity of addition with nested parentheses. -/)]
theorem nested_parens (a b c : Nat) : (a + (b + c)) = ((a + b) + c) := by
  -- This uses associativity of natural number addition
  omega

-- Function with multiple bracket types
-- Demonstrates parentheses and square brackets in combination
@[blueprint "bracket:function"
  (title := "Mixed Brackets")
  (statement := /-- A function with mixed bracket types (parentheses and square brackets). -/)]
def bracket_function (f : Nat → Nat) (xs : List Nat) : List Nat :=
  xs.map (fun x => f (f x))  -- nested function application

-- Type with implicit arguments (curly braces)
-- Shows curly braces for implicit type parameters
@[blueprint "bracket:types"
  (title := "Type Brackets")
  (keyDeclaration := true)
  (message := "Shows implicit type brackets")
  (statement := /-- A theorem with implicit type parameters using curly braces. -/)]
theorem type_example {α : Type} (s : Set α) (x : α) (h : x ∈ s) : x ∈ s := h

-- Deeply nested brackets (4 levels)
-- Each level should have a different color
@[blueprint "bracket:deep"
  (title := "Deep Nesting")
  (statement := /-- Definition with 4 levels of nested parentheses. -/)]
def deep_nesting : Nat :=
  (((1 + 2) + 3) + 4)  -- 4 levels deep, each a different color

-- Complex expression with all bracket types
-- Combines parentheses, square brackets, and curly braces
@[blueprint "bracket:complex"
  (title := "All Bracket Types")
  (keyDeclaration := true)
  (message := "Combines all three bracket types")
  (statement := /-- A complex expression using all bracket types together. -/)]
def all_brackets {α : Type} (xs : List α) (p : α → Bool) : Option (List α) :=
  if xs.isEmpty then
    none
  else
    some (xs.filter p)

end SBSTest.BracketDemo
