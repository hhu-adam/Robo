import Game.Metadata

World "Iso"
Level 1
Title "" -- "Bijektivität"

/-
Introduction
"
**Isosoph**:  Natürlich haben auch wir etwas für euch vorbereitet.
"
-/
Introduction "`INTRO` Intro Iso L01"

open Function

Statement :
    let f := fun (n : ℤ) ↦ n + 1
    Bijective f := by
  /-
  Hint "
    **Robo** *(flüsternd)*: `Bijective f` ist als `Injective f ∧ Surjective f` definiert.

    **Du**: Dann ist das ja ganz simpel!"
  -/
  Hint "Remind that `Bijective f` is defined as `Injective f ∧ Surjective f`"
  unfold Bijective
  constructor
  · intro a b hab
    simp [f] at hab
    assumption
  · intro y
    use y-1
    simp [f]

NewDefinition Function.Bijective
TheoremTab "Function"

/-
Conclusion
"
**Isososoph**: Super.  Dann können wir das hier, glaube ich, alles überspringen …

Er legt ein paar Blätter zur Seite.
"
-/
Conclusion "`CONC` Conclusion Iso L01"
