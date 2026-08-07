import Game.Metadata

World "Hamel"
Level 4

open Finsupp

Introduction "Intro Hamel L04"

/- This level introduces `equivFunOnFinite`. -/

Statement : (equivFunOnFinite.symm ![1, (2 : ℝ)]) 0 = ![1, 2] 0 := by
  simp

NewDefinition Finsupp.equivFunOnFinite

TheoremTab "LinearAlgebra"
