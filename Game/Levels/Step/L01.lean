import Game.Metadata


World "Step"
Level 1

open Finsupp

/- This level introduces `equivFunOnFinite`. -/

/---/
DefinitionDoc Finsupp.equivFunOnFinite as "Finsupp.equivFunOnFinite" in "LinearAlgebra"

/---/
TheoremDoc Finsupp.coe_equivFunOnFinite_symm as "Finsupp.coe_equivFunOnFinite_symm" in "LinearAlgebra"

Statement : (equivFunOnFinite.symm ![1, (2 : ℝ)]) 0 = ![1, 2] 0 := by
  Hint "[Hint cesymm] `Finsupp.coe_equivFunOnFinite_symm` is useful here. "
  rw [coe_equivFunOnFinite_symm]

NewDefinition Finsupp.equivFunOnFinite
NewTheorem Finsupp.coe_equivFunOnFinite_symm

TheoremTab "LinearAlgebra"
