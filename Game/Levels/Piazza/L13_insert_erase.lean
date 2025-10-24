import Game.Metadata

World "Piazza"
Level 13

Title ""

/-
Introduction "
  **Fin**:  Und, was meint ihr – sind jetzt wieder alle Pistazien zu Hause?
"
-/
Introduction "`INTRO` Intro Piazza L13"

/---/
TheoremDoc Finset.insert_erase as "insert_erase" in "Set"

namespace Finset
open Classical -- otherwise need `[h : DecidableEq A]` in the statement
               -- open scoped Classical also works in vscode and compliles without error,
               -- but somehow leads to error in this level when deployed locally with npm start
Statement insert_erase {A : Type} {s : Finset A} {a : A} (h : a ∈ s) :
  insert a (Finset.erase s a) = s := by
  ext b
  simp
  -- Hint (hidden := true) "
  --   **Fin**: Mach doch eine Fallunterscheidung, ob `{b} = a` ist oder nicht.
  --"
  Hint (hidden := true) "Try proof by cases, if `{b} = a`"
  Branch
    constructor
    -- Hint "**Fin**:  Ja, so kann man das angehen."
    Hint "Story"
    · intro h
      obtain h₁ | ⟨ h₂, h₃ ⟩ := h
      rw [← h₁] at h
      assumption
      assumption
    · intro hb
      by_cases heq: b = a
      left
      assumption
      right
      constructor
      assumption
      assumption
  by_cases heq : b = a
  · rw [heq]
    tauto
  · simp [heq]

TheoremTab "Set"

/-
Conclusion "Die Kinder lachen, bilden einen Kreis um euch um singen ein Lied in einer Sprache,
die ihr beide nicht versteht.  Dann laufen sie davon.

**Robo**:  Ich glaube, wir können weiterfliegen."
-/
Conclusion "`CONC` Conclusion Piazza L13"
