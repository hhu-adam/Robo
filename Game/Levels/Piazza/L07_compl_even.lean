import Game.Metadata

World "Piazza"
Level 7

Title ""

/-
Introduction
"
**Ext**:  Das Komplement ist auch nur eine Menge.
"
-/
Introduction "Intro Piazza L07: the complement `Aᶜ` collects exactly the elements *not* in `A`.
It is the same as `(univ : Set ℕ) \\ A`."

open Set

Statement :
    {(n : ℕ) | Even n}ᶜ  = {n | Odd n} := by
  Hint (hidden := true) "[Hint cqvs] Try `ext`"
  ext i
  Hint (hidden := true) "Perform `simp` again"
  simp

/-- -/
DefinitionDoc Set.compl as "·ᶜ" in "Set"

NewDefinition Set.compl
TheoremTab "Set"

Conclusion "Conclusion Piazza L07: the complement `Aᶜ` is `univ \\ A`."
