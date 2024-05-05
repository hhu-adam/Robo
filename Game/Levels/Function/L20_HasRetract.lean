import Game.Metadata

World "Function2"
Level 20


Title "Injections with nonempty domain have retract."


Introduction
"
  In this level you show that an injective function with a nonempty domain has a left inverse.
"

open Function Set

-- attribute [local instance] Classical.propDecidable

Statement Injective.hasLeftInverse [Nonempty A] (f : A → B) (hf : Injective f) :
    HasLeftInverse f := by
  classical
  let finv : B → A := fun b => if h : ∃ x, f x = b then h.choose else Classical.arbitrary A
  use finv
  simp [LeftInverse]
  intro x
  apply hf
  simp only [finv, dif_pos (⟨x, rfl⟩ : ∃ x', f x' = f x)]
  apply Exists.choose_spec (⟨x, rfl⟩ : ∃ x', f x' = f x)

NewTheorem dif_pos
