/-
Generate HTML output from the SBS-Test Blueprint document.
This executable produces `.lake/build/verso/blueprint_verso.html`.
-/
import SBSBlueprint
import SBSTest.Blueprint

open Verso.Genre.SBSBlueprint.Main

def main : IO UInt32 :=
  sbsBlueprintMain (%doc SBSTest.Blueprint) (config := {
    outputDir := ".lake/build/verso",
    buildDir := ".lake/build",
    title := "SBS-Test Blueprint",
    outputFileName := "blueprint_verso",
    verbose := true,
  })
