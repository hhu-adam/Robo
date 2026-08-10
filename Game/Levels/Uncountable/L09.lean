import Game.Metadata

World "Uncountable"
Level 9

Introduction "Intro Uncountable L09"

universe u

open Module

noncomputable section

Statement {K V ι : Type u} [Field K] [AddCommGroup V]
    [Module K V] [Finite ι] (h_basis : Basis ι K V) : V ≃ₗ[K] (ι → K) := by
  Hint "[Hint basEqF] Once you fix a basis indexed by a *finite* type `ι`, every vector is
    determined by its tuple of coordinates, and reading off coordinates is linear. That is
    what `Basis.equivFun` packages."
  Hint (hidden := true) "[basEqfh] `{h_basis}.equivFun` is the equivalence you are after."
  apply h_basis.equivFun

NewDefinition Module.Basis.equivFun LinearEquiv LinearMap
