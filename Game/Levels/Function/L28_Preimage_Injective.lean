import Game.Metadata


World "Function2"
Level 28

Title "Preimage of surjective is injective"

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

Statement preimage_injective {f : A → B} : Injective (preimage f) ↔ Surjective f := by
  constructor
  · intro hinj y
    change (f ⁻¹' {y}).Nonempty
    rw [nonempty_iff_ne_empty]
    rw [← preimage_empty]
    apply hinj.ne_iff.mpr
    simp
  · intro hsurj
    intro S T heq
    Branch
      rw [← image_preimage_eq S hsurj, ← image_preimage_eq T hsurj, heq]
    apply Subset.antisymm
    · intro y hy
      obtain ⟨x, hx⟩ := hsurj y
      rw [← hx] at hy
      have : x ∈ f⁻¹' S := by exact mem_preimage.mp hy
      rw [heq] at this
      rw [← hx]
      exact mem_preimage.mp this
    · intro y hy
      obtain ⟨x, hx⟩ := hsurj y
      rw [← hx] at hy
      have : x ∈ f⁻¹' T := by exact mem_preimage.mp hy
      rw [← heq] at this
      rw [← hx]
      exact mem_preimage.mp this
