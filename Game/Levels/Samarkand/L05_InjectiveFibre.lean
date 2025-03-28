import Game.Levels.Samarkand.L04_SurjectiveImagePreimage

World "Samarkand"
Level 5

Title "" -- "Range of Injective"

Introduction "
  **Arapuka**:  Ich habe auch noch eine Frage zu injektiven Abbildungen.
"

open Set

#check Set.singleton

/---/
TheoremDoc Function.Injective.exists_unique_of_mem_range as "Injective.exists_unique_of_mem_range" in "Function"

namespace Function

Statement Injective.exists_unique_of_mem_range {A B : Type} {f : A → B} (hf : Injective f)
    {b : B} (hb : b ∈ range f) :
    ∃! a, f a = b := by
  Hint "**Du**:  Bei `∃! a` konstruiere ich mir zunächst das Element `a`, das ich verwenden möchte …

  **Robo**: … und dann wendest du `use a` und `simp` an.  Genau.
  "
  obtain ⟨a, ha⟩ := hb
  use a
  simp -- TODO: can this be integrated into mathlib `use`?
  constructor
  · assumption
  · intro a' ha'
    apply hf
    rw [ha',ha]

Conclusion "
  Arapuka liegt immer noch ganz regungslos, aber sie sieht glücklich aus.
"
