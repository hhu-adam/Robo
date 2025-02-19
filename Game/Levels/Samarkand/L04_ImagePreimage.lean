import Game.Metadata


World "Samarkand"
Level 4
Title "" -- ""

open Function Set

Statement {A B : Type} {f : A → B} (hf : Surjective f) (s : Set B) :
f '' (f ⁻¹' s) = s := by
  ext b
  simp
  constructor
  · apply image_preimage_subset -- Lvl 1
  · intro hb
    obtain ⟨a, ha⟩ := hf b
    use a
    constructor
    · rw [ha]
      assumption
    · assumption
