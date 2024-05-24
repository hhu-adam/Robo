import Game.Metadata


World "FunctionInj"
Level 8

Title "Preimage of the inverse"

Introduction
"

The image of a set `S : Set A` along a  function `f : A → B` is the set of all elements
`b : B` that are the image of some element `a : A` in `S`. We denote it by `f '' S` and
define it as below.
```
f '' S = {b : B | ∃ a : A, a ∈ S ∧ f a = b}
```

Note that an element of the image is a triple `⟨b, a, h⟩` where `b` is the image of `a` and `h`
is the proof that `a` is in `S` and `f a = b`.

The image of function with a left in
verse is a subset of the preimage of the inverse of
the same subset.
"

open Function Set

Statement image_subset_preimage_of_inverse {f : A → B} {g : B → A} (hL : LeftInverse g f)
    (S : Set A) :
    f '' S ⊆ g ⁻¹' S := by
  intro b hb
  obtain ⟨x, hx, e⟩ := hb
  dsimp [LeftInverse] at hL
  rw [← hL x, e] at hx
  Branch
    apply hx
  assumption
