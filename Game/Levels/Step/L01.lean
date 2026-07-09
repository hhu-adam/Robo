import Game.Metadata


World "Step"
Level 1

open Finsupp

/- This level introduces `equivFunOnFinite`. -/

/---/
DefinitionDoc Finsupp.equivFunOnFinite as "Finsupp.equivFunOnFinite" in "LinearAlgebra"

Statement : (equivFunOnFinite.symm ![1, (2 : ℝ)]) 0 = ![1, 2] 0 := by
  simp

NewDefinition Finsupp.equivFunOnFinite

TheoremTab "LinearAlgebra"
