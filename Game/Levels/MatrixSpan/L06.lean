import Game.Metadata




World "Span"
Level 6

Title "" -- "Span"

/- # Introduction

-/

open Real Function Set Finset

Statement (M : Type*) [AddCommMonoid M] [Module ℝ M] (S : Submodule ℝ M) (x : M) (r : ℝ)
    (hr : r ≠ 0) : r • x ∈ S ↔ x ∈ S := by
  --apply Submodule.smul_mem_iff
  --assumption
  constructor
  · intro hrxS
    rw [← inv_smul_smul (Units.mk0 r hr) x]
    apply Submodule.smul_mem
    apply hrxS
  · intro hxS
    --simpa using (Submodule.smul_mem S r hxS)
    apply Submodule.smul_mem
    assumption

/---/
TheoremDoc Submodule.smul_mem as "Submodule.smul_mem" in "LinearAlgebra"

/---/
TheoremDoc inv_smul_smul as "inv_smul_smul" in "LinearAlgebra"

/---/
DefinitionDoc Units.mk0 as "Units.mk0" in "LinearAlgebra"

NewTheorem Submodule.smul_mem inv_smul_smul
NewDefinition Units.mk0
