/-
Generate HTML output from the SBS-Test Paper document.
This executable produces `.lake/build/runway/paper_verso.html`.
-/
import SBSBlueprint
import SBSTest.Paper

open Verso.Genre.SBSBlueprint.Main

def main : IO UInt32 :=
  sbsBlueprintMain (%doc SBSTest.Paper) (config := {
    outputDir := ".lake/build/runway",
    buildDir := ".lake/build",
    title := "SBS-Test Paper",
    outputFileName := "paper_verso",
    verbose := true,
  })
