import Game.Metadata

World "FunctionBij"
Level 1
Title "Bijektivität"

Introduction
"
**Du**: Ehm, und wie kommen wir da wieder raus?

**Gelehrter**: Gerne zeige ich euch den Weg, nachdem ihr mir auch noch folgendes erklärt:
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
    simp [f] at hab -- TODO: is there a better way?
    assumption
  · intro y
    use y-1
    simp [f]

NewDefinition Function.Bijective
TheoremTab "Function"

Conclusion
"
Zufrieden drückt euch der Gelehrte eine neue Fackel in die Hand und
zeigt euch den Weg nach draußen.
"
