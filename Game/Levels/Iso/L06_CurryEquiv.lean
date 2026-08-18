import Game.Metadata

universe u₁ u₂ u₃

World "Iso"
Level 6

/-
Introduction
"
In this level, you will learn about currying. Currying is the process of transforming a function that takes multiple arguments into a function that takes one argument and returns another function that takes the next argument, and so on, until all arguments have been supplied. This is useful because it allows you to partially apply a function, which means you can supply some of the arguments now and the rest later.

This insight was first made explicit separately by Moses Ilyich Schönfinkel in the 19th century and later in the 20th century by Haskell Curry.

"
-/
Introduction "Intro Iso L06"

open Function

Statement {A : Type u₁} {B : Type u₂} {C : Type u₃} :
    (A × B → C) ≃ (A → B → C) := by
  Hint "[Hint h4nzq] `Function.curry` goes from `A × B → C` to `A → B → C`, and
  `Function.uncurry` back again."
  refine' {toFun := curry, invFun := uncurry, left_inv := _, right_inv := _}
  · simp [LeftInverse]
  · simp [LeftInverse, RightInverse]

NewDefinition Function.curry Function.uncurry
