import Game.Metadata

World "Function"
Level 5

Title "Semiconjugate"
Introduction
"

"

open Function Nat

Statement {f : α → ℕ} {z : α} (h : f z = 0) {g : α → α}
    (hs : f ∘ g = succ ∘ f) : Surjective f := by
  intro n
  induction n with n hn
  · use z
  · rcases hn with ⟨a, ha⟩
    use g a
    Hint "
    `fun_arg`
        "
    rw [← comp_apply (f:= f) (g:= g)]
    rw [hs]
    rw [comp_apply]
    rw [ha]
