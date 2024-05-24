import Game.Metadata


World "FunctionInj"
Level 7

Title "Choosing an arbitrary element of a nonempty type."


Introduction
"
  In this level you show that an injective function with a nonempty domain has a left inverse.
"

open Function Set Nat


Statement {A : Type*} [Nonempty A] (f : ℕ → A) :
    ∃ g : ℤ → A, ∀ n : ℕ, (f n = g n) := by
  let g : ℤ → A := fun
    | .ofNat n => f n
    | .negSucc _ => Classical.arbitrary A
  use g
  intro n
  rfl

-- more difficult version
example {A : Type*} [Nonempty A] (f : ℕ → A) :
    ∃ g : ℤ → A, ∀ n > 0, (f n = g n) := by
  let g : ℤ → A := fun
    | 0 => Classical.arbitrary A
    | Nat.succ n => f (succ n)
    | .negSucc _ => Classical.arbitrary A
  use g
  intro n hn
  rw [← Nat.succ_pred_eq_of_pos hn]

NewTheorem Classical.arbitrary
