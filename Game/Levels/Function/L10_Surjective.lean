import Game.Metadata


World "Function"
Level 9

Title "A function which semiconjugates an endofunction to the
successor function is surjective."
Introduction
"

"

open Function Nat

Statement {A : Type} {f : A → ℕ} (h : ∃ a : A, f a = 0) {g : A → A}
    (hs : f ∘ g = succ ∘ f) (n : ℕ) : ∃ a, f a = n := by
  Hint "Induktion über `{n}`"
  induction n with n hn
  · assumption
  · obtain ⟨a, ha⟩ := hn
    Hint "
      **Robo**: Siehst du die Annahme `{hs} : f ∘ g = succ ∘ f`?

      **Du**: Ja.

      **Robo**: Um eine Gleichheit von Funktionen zu verwenden, willst du
      oft `apply congr_fun at {hs}` sagen! Das wandelt die Gleichung
      `f₁ = f₂` in `∀ x, f₁ x = f₂ x` um.
    "
    use g a
    Branch
      -- TODO: Hints for this branch!
      apply congr_fun at hs
      have hs' := hs a
      rw [comp_apply, comp_apply] at hs'
      rw [hs']
      rw [ha]
    rw [← ha]
    apply congr_fun hs
