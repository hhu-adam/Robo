import Game.Metadata


World "FunctionSurj"
Level 14

Title "Every function with nonempty fibres has a right inverse."


Introduction
"
The preimage of set `S` under a function `f`, denoted by `f ⁻¹' S` is the set of all elements
`x` in the domain of `f` such that `f x` is in `S`.

```
f ⁻¹' S = {x | f x ∈ S}
```

We call the preimage `f ⁻¹' { b }` of the singleton `{ b }` the fiber of `b`.

"

open Function

Statement {A B : Type} (f : A → B) (nonempty_fibre : ∀ b : B, Set.Nonempty (f ⁻¹' { b })) :
    HasRightInverse f := by
  Hint "
      Since we know that for each `b : B`, the fiber is nonempty, we can choose some element of that fibre using the axiom of choice.
      The tactic `choose g hg using nonempty_fibre` creates a function which chooses an `a : A` and `hg` witnesses that `a` is in the fiber of `b`.
      "
  choose g hg using nonempty_fibre
  use g
  assumption

NewTactic choose
