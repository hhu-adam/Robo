import Game.Metadata

World "Iso"
Level 3

/-
Introduction
"
In this level, you will learn about currying. Currying is the process of transforming a function
that takes multiple arguments into a function that takes one argument and returns another function
that takes the next argument, and so on, until all arguments have been supplied. This is useful
because it allows you to partially apply a function, which means you can supply some of the
arguments now and the rest later.

This insight was first made explicit separately by Moses Ilyich Schönfinkel in the 19th
century and later in the 20th century by Haskell Curry.
"
-/
Introduction "Intro Iso L03"

open Function

Statement {A B C : Type*} :
    (A × B → C) ≃ (A → B → C) := by
  Hint "[Hint m2rqd] You have been reading `ℕ → A → B` as a map into a function space since
    Epo, and Cantor's diagonal argument feeds two arguments into `f : A → A → Y` the same way.
    Such a function of two arguments is really a function on the product. "
  Hint "[Hint w3knf] An equivalence `A ≃ B` is not a proposition but *data*:
    a map `toFun : A → B`, a backwards map `invFun : B → A`,
    and two proofs `left_inv`, `right_inv` saying that these undo each other."
  Hint "[Hint h4nzq] `Function.curry` goes from `A × B → C` to `A → B → C`, and
  `Function.uncurry` back again."
  Hint (hidden := true) "[Hint p7ubs] A new tactic: `refine ⟨curry, uncurry, ?_, ?_⟩` fills in the
    two maps and leaves the two proofs as goals."
  refine ⟨curry, uncurry, ?_, ?_ ⟩
  · simp [LeftInverse]
  · simp [LeftInverse, RightInverse]

NewTactic refine

NewDefinition Equiv Function.curry Function.uncurry
