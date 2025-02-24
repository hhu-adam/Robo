import Game.Metadata

World "Piazza"
Level 2

Title "" -- "Schnitt und Vereinigung"

Introduction
"
Bei Gleichheit von Mengen kann durch ein Standardschema aus 3
Schritten bewiesen werden.

Hier als Beispiel die Distributivität vom Schnitt `∩` über die
Vereinigung `∪`.
"

open Set

Statement (A B C : Set ℕ) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  Hint "Die Taktik `ext x` zeigt eine Mengengleichheit `A = B`
  durch `x ∈ A ↔ x ∈ B`."
  ext x
  Hint "Als zweiter Schritt kann `simp` verwendet werden, um die Definition
  von `∈ …` einzusetzen.

  `simp` braucht hier Aussagen wie
  - `{x} ∈ {A} ∩ _ ↔ {x} ∈ {A} ∧ {x} ∈ _`
  - `{x} ∈ {B} ∪ {C} ↔ {x} ∈ {B} ∨ {x} ∈ {C}`
  deren Namen müssen wir aber nich lernen
  "
  simp only [mem_inter_iff, mem_union]
  Hint "Jetzt haben wir die Mengengleichung auf Logik
  zurückgeführt und als dritter Schritt kann `tauto` den Rest übernehmen."
  tauto

NewTactic ext
NewDefinition Set.union Set.inter
TheoremTab "Set"

Conclusion ""
