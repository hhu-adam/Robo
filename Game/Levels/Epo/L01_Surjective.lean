import Game.Metadata

World "Epo"
Level 1

Title ""

/-
Introduction "
Die Fahrt ist tatsächlich kurz und schmerzlos.
Und euch wird tatsächlich ein großen Empfang bereitet.
Nachdem sich die erste Aufregung gelegt hat, werdet ihr aber auch hier mit Aufgaben konfrontiert."
-/
Introduction "Intro Epo L01"

open Function

Statement :
    let f := fun (n : ℤ) ↦ n + 1
    Surjective f := by
  /-
  Hint "**Du**: Vermute ich richtig, dass die Definition von `Surjective f` ist: `∀ y, (∃ x, f x = y)`?

  **Robo**: Glaub schon.  Du könntest ja mal mit `unfold Surjective` hineinsehen. Musst da aber auch nicht."
  -/
  Hint "Confirm that `Surjective f` is defined as `∀ y, (∃ x, f x = y)` via `unfold Surjective`"
  unfold Surjective
  intro y
  use y-1
  Branch
    simp [f]
  ring

/--
`Surjective f` bedeutet naheliegenderweise, dass die Abbildung `f` surjektiv ist.
Mit `unfold Surjective` (bzw. `unfold Surjective at h`) kann man leicht nachsehen, was das
in Quantorenschreibweise konkret bedeutet.
-/
DefinitionDoc Function.Surjective as "Surjective" in "Function"
NewDefinition Function.Surjective
TheoremTab "Function"

Conclusion ""
