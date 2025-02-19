import Game.Metadata


World "Mono"
Level 10

Title ""

Introduction ""

open Function Set

-- Could be done much earlier; needed as a have statement in the Boss level
-- Presumably needs hints!!
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
