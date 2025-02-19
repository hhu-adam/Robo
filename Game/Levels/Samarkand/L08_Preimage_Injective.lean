import Game.Metadata

import Game.Levels.Samarkand.L06

World "Samarkand"
Level 8

Title "" -- "Preimage of surjective is injective"

Introduction
"
Given a function `f : A → B` we obtain a function `preimage f : Set B → Set A`
by taking the preimage of sets of `B`. Recall that
```
preimage f S = f ⁻¹' S = {a | f a ∈ S}
```

Show that `preimage f` is injective iff f is surjective.

"

open Function Set

Statement preimage_injective {A B : Type} {f : A → B} : Injective (preimage f) ↔ Surjective f := by
  constructor
  · Branch
      -- Marcus' solution
      intro h_inj
      intro b
      by_contra h_contra
      push_neg at h_contra
      -- have h₁ : preimage f ∅ = ∅ := by
      --   simp
      have h₂ : preimage f {b} = ∅ := by
        rw [eq_empty_iff_forall_not_mem]
        intro a
        specialize h_contra a
        assumption
      have : preimage f ∅ = preimage f {b}
      rw [preimage_empty,h₂]
      apply h_inj at this
      symm at this
      rw [eq_empty_iff_forall_not_mem] at this
      apply this b
      simp
    intro hinj y
    rw [← preimage_not_empty_iff]
    -- change f ⁻¹' {y} ≠ ∅ -- TODO: it's displayed not nicely :(
    have g : f ⁻¹' ∅ = ∅ := by simp
    rw [← g]
    -- or: `rw [← preimage_empty]`
    rw [Injective.ne_iff hinj]
    simp
  · intro h_surj
    intro s s' hs
    apply congr_arg (image f) at hs
    rw [Surjective.image_preimage h_surj] at hs
    rw [Surjective.image_preimage h_surj] at hs
    assumption
