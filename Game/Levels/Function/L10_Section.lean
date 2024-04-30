import Game.Metadata

World "Function"
Level 10

Title "Range of Surjection"


Introduction
"
The preimage of set `S` under a function `f`, denoted by `f ⁻¹' S` is the set of all elements
`x` in the domain of `f` such that `f x` is in `S`.

```
f ⁻¹' S = {x | f x ∈ S}
```

We call the preimage `f ⁻¹' { b }` of the singleton `{ b }` the fiber of `b`.

The theorem `surjective_iff_hasRightInverse` says that a function `f : A → B` is
surjective if and only if it has a right inverse. In this level, you will prove
a closely related statement: that a function with nonempty fibers has a right inverse.
"

open Function

Statement (nonempty_fibre : ∀ b : B, Set.Nonempty (f ⁻¹' { b })) : HasRightInverse f := by
  Branch
      Hint "
      ...
      "
      use fun b ↦ (nonempty_fibre b).choose
      intro b
      dsimp
      Hint "
      ...
      "
      exact (nonempty_fibre b).choose_spec
  Hint "
      Since we know that for each `b : B`, the fiber is nonempty, we can choose some element of that fibre using the axiom of choice.
      The tactic `choose g hg using nonempty_fibre` creates a function which chooses an `a : A` and `hg` witnesses that `a` is in the fiber of `b`.
      "
  choose g hg using nonempty_fibre
  use g
  exact hg
