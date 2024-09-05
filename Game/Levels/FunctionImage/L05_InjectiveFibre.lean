import Game.Metadata

World "FunctionImage"
Level 5

Title "Range of Injective"

Introduction
"
For an injective function `f : A → B` the fibres of the elements in the range
are singletons.
"

open Function Set

#check Set.singleton

Statement Injective.exists_unique_of_mem_range {A B : Type} {f : A → B} (hf : Injective f)
    {b : B} (hb : b ∈ range f) :
    ∃! a, f a = b := by
  obtain ⟨a, ha⟩ := hb
  use a
  dsimp only -- TODO: can this be integrated into Mathlib `use`?
  constructor
  · assumption
  · intro a' ha'
    apply hf
    rw [ha',ha]

NewDefinition Set.Range
