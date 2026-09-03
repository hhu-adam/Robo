import Game.Metadata

World "Uncountable"
Level 11

Introduction "Intro Uncountable L11"

universe u

open Module

noncomputable section

Statement {K V : Type u} [Field K] [AddCommGroup V] [Module K V] :
    ∃ ι : Type u, Nonempty (Basis ι K V) := by
  Hint "[Hint basisEx] Every vector space has a basis. In Mathlib it is given by
    `Basis.ofVectorSpace K V`, indexed by the type `Basis.ofVectorSpaceIndex K V`."
  use Basis.ofVectorSpaceIndex K V
  Hint (hidden := true) "[Hint nempB] `Nonempty` only asks you to produce an element, so
    `constructor` leaves you with the task of exhibiting an actual basis."
  constructor
  apply Basis.ofVectorSpace

NewDefinition Module.Basis.ofVectorSpace Module.Basis.ofVectorSpaceIndex
