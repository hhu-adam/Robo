import Game.Metadata


World "FunctionSurj"
Level 5

Title "Left inverse"


Introduction
"
A function `g : B → A` is a left inverse of a function `f : A → B` if for all `a : A`,
`g (f a) = a`.

"

open Function

Statement {A B : Type} {f : A -> B} {g : B -> A} :
    RightInverse g f ↔ LeftInverse f g :=
  by
  Hint (hidden := true) "
    Actually, in Lean, we have `RightInverse g f = LeftInverse f g` by definition.
  "
  Branch
    simp [Function.RightInverse, LeftInverse]
  tauto


TheoremTab "Function"
NewDefinition Function.LeftInverse
