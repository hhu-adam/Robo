import Game.Metadata

open Function Set

World "Samarkand"
Level 1
Title "Bild/Urbild"

Introduction "
`f '' S` ist das Bild,
`f ⁻¹' V` das Urbild,

`f '' S := {f a | a ∈ S}`
`f ⁻¹' V := {a | f a ∈ V}`
"

/--  -/
TheoremDoc Set.image_preimage_subset as "image_preimage_subset" in "Set"

Statement Set.image_preimage_subset {A B : Type} (f : A → B) (S : Set B) :
    f '' (f ⁻¹' S) ⊆ S := by
  intro b
  intro hb
  simp at hb
  obtain ⟨a, ha₁, ha₂⟩ := hb
  rw [ha₂] at ha₁
  assumption

NewDefinition Set.image Set.preimage
