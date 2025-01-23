import Game.Metadata


World "FunctionInj"
Level 10

Title "Injections have a left inverse, and vice versa"

Introduction
"
"

open Function Set


-- TODO: new level with this!
-- Needed as a have statement in the Boss level
Statement {A B : Type} [hA : Nonempty A] (f : A → B ) : ∀ b : B, ∃ a : A, f a = b ∨ ¬ ∃ a' : A , f a' = b   := by
  obtain ⟨a₀⟩ := hA
  intro b
  by_cases hb : ∃ a' : A, f a' = b
  · obtain ⟨a,ha⟩ := hb
    use a
    left
    assumption
  use a₀
  right
  assumption


-- mathlib: Function.injective_iff_hasLeftInverse
Statement injective_iff_hasLeftInverse {A B : Type} [hA : Nonempty A]  (f : A → B) :
  Injective f ↔ HasLeftInverse f := by
  constructor
  · intro hf
    have : ∀ b : B, ∃ a : A, f a = b ∨ ¬ ∃ a' : A , f a' = b := by
      /- exactly a previous level, now without hints -/
      obtain ⟨a₀⟩ := hA
      intro b
      by_cases hb : ∃ a' : A, f a' = b
      · obtain ⟨a,ha⟩ := hb
        use a
        left
        assumption
      use a₀
      right
      assumption
    choose g hg using this
    use g
    intro a
    apply hf
    obtain hpos | hneg := hg (f a)
    · assumption
    · push_neg at hneg
      have : f a ≠ f a := hneg a
      contradiction
  · /- Injective f → HasLeftInverse f
       exactly a previous level, now without hints-/
    intro hL
    intro a a' ha
    obtain ⟨g, hg⟩ := hL
    apply congr_arg g at ha
    unfold LeftInverse at hg
    rw [hg a, hg a'] at ha
    assumption
