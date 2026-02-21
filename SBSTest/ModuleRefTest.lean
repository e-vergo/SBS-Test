/-
SBS-Test: Module Reference Test
Tests the `\inputleanmodule{ModuleName}` LaTeX command.

This module contains declarations that will be referenced via module import
rather than individual `\inputleannode{label}` commands.
-/
import Dress
import Mathlib.Tactic

namespace SBSTest.ModuleRefTest

/-! ## Module Reference Test Declarations

These declarations test the `\inputleanmodule{SBSTest.ModuleRefTest}` feature,
which imports all blueprinted declarations from a module at once.
-/

@[blueprint "mod:first"
  (title := "Module Test First")
  (statement := /-- First declaration in the module reference test. -/)
  (proof := /-- Defined as the constant value $42$. -/)]
def firstDef : Nat := 42

@[blueprint "mod:second"
  (title := "Module Test Second")
  (statement := /-- Second declaration, depends on the first. \uses{mod:first} -/)
  (proof := /-- A simple proof. -/)]
theorem secondThm : firstDef = 42 := rfl

end SBSTest.ModuleRefTest
