import Game.Metadata

World "Uncountable"
Level 10

universe u

open Module

noncomputable section

Statement {K V : Type u} [Field K] [AddCommGroup V] [Module K V] :
    ∃ ι : Type u, Nonempty (Basis ι K V) := by
  Hint "[Hint basisEx] Every vector space has a basis. In Mathlib it is given by
    `Basis.ofVectorSpace K V`, indexed by the type `Basis.ofVectorSpaceIndex K V`."
  use Basis.ofVectorSpaceIndex K V
  constructor
  apply Basis.ofVectorSpace

/---/
DefinitionDoc Module.Basis.ofVectorSpace as "Basis.ofVectorSpace" in "LinearAlgebra"

/---/
DefinitionDoc Module.Basis.ofVectorSpaceIndex as "Basis.ofVectorSpaceIndex" in "LinearAlgebra"

NewDefinition Module.Basis.ofVectorSpace Module.Basis.ofVectorSpaceIndex
