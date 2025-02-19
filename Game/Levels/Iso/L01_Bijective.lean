import Game.Metadata

World "Iso"
Level 1
Title "" -- "Bijektivität"

Introduction
"
**Isososoph**:  Natürlich haben auch wir etwas für euch vorbereitet.
"

open Function

Statement :
    let f := fun (n : ℤ) ↦ n + 1
    Bijective f := by
  Hint "
    **Robo** *(flüsternd)*: `Bijectve f` ist als `Injective f ∧ Surjective f` definiert.

    **Du**: Dann ist das ja ganz simpel!"
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

Conclusion
"
**Isososoph**: Super.  Dann können wir das hier, glaube ich, alles überspringen …

Er legt ein paar Blätter zur Seite.
"
