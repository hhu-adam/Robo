import Game.Metadata

World "Uncountable"
Level 9

Introduction "Intro Uncountable L09"

universe u

open Module

noncomputable section

Statement {K V ι : Type u} [Field K] [AddCommGroup V]
    [Module K V] [Finite ι] (h_basis : Basis ι K V) : V ≃ₗ[K] (ι → K) := by
  apply h_basis.equivFun

/---/
DefinitionDoc Module.Basis.equivFun as "Basis.equivFun" in "LinearAlgebra"

NewDefinition Module.Basis.equivFun LinearEquiv LinearMap
