import Game.Metadata


World "Step"
Level 11

open Finset

/- In the previous level you showed that a nonempty finite set of reals has a
smallest element. Mathlib packages this smallest element as `Finset.min'`.
This level introduces `Finset.min'_mem`. -/

/---/
DefinitionDoc Finset.min' as "Finset.min'" in "Set"

/---/
TheoremDoc Finset.min'_mem as "Finset.min'_mem" in "Set"

Statement (s : Finset ℝ) (hs : s.Nonempty) : s.min' hs ∈ s := by
  apply Finset.min'_mem

NewDefinition Finset.min'
NewTheorem Finset.min'_mem

TheoremTab "Set"
