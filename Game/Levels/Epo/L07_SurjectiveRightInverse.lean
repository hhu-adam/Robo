import Game.Metadata


World "Epo"
Level 7

Title "Every surjection has a right inverse"


Introduction
"
The preimage of set `S` under a function `f`, denoted by `f ⁻¹' S` is the set of all elements
`x` in the domain of `f` such that `f x` is in `S`.

```
f ⁻¹' S = {x | f x ∈ S}
```

`HasRightInverse.surjective`

"

open Function Set

Statement {A B : Type} (f : A → B) :
    Surjective f ↔ HasRightInverse f := by
  constructor
  · intro hs
    choose g hg using hs
    unfold HasRightInverse
    use g
    assumption
  · -- this is `Function.HasRightInverse.surjective`
    intro ⟨g, inv⟩
    intro b
    use g b
    apply inv

TheoremTab "Function"
