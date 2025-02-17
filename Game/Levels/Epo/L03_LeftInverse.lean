import Game.Metadata


World "Epo"
Level 3

Title "Left inverse"


Introduction
"
A function `g : B → A` is a left inverse of a function `f : A → B` if for all `a : A`,
`g (f a) = a`.

"

open Function

Statement {A B : Type} {f : A -> B} {g : B -> A} :
    RightInverse g f ↔ LeftInverse f g := by
  Hint (hidden := true) "
    Actually, in Lean, we have `RightInverse g f = LeftInverse f g` by definition.
  "
  Branch
    unfold Function.RightInverse
    rfl
  tauto

/-- `Function.RightInverse f g` is als `LeftInverse g f` definiert.

Man muss `Function.` anfügen, da Mathlib noch eine andere Definition `RightInverse`
besitzt, weshalb ein simples `RightInverse` nicht eindeutig wäre. -/
DefinitionDoc Function.RightInverse as "RightInverse"

/---/
DefinitionDoc Function.LeftInverse as "LeftInverse"

TheoremTab "Function"
NewDefinition Function.RightInverse Function.LeftInverse
