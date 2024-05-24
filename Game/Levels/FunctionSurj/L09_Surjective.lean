import Game.Metadata


World "FunctionSurj"
Level 9

Title "A function which semiconjugates an endofunction to the
successor function is surjective."
Introduction
"

"

open Function Nat

Statement {f : A → ℕ} (h : ∃ a : A, f a = 0) {g : A → A}
    (hs : f ∘ g = succ ∘ f) : Surjective f := by
  obtain ⟨a₀, ha₀⟩ := h
  intro n
  Hint "Induktion über `{n}`"
  induction n with n hn
  · use a₀
  · Hint "
      **Robo**: Siehst du die Annahme `{hs} : f ∘ g = succ ∘ f`?

      **Du**: Ja.

      **Robo**: Um eine Gleichheit von Funktionen zu verwenden, willst du
      oft `apply congr_fun at {hs}` sagen! Das wandelt die Gleichung
      `f₁ = f₂` in `∀ x, f₁ x = f₂ x` um.
    "
    apply congr_fun at hs
    rcases hn with ⟨a, ha⟩
    use g a
    Hint (hidden := true) "`simp_rw [comp_apply] at {hs}` hilft damit du `{hs}` mit `rw`
    verwenden kannst."
    simp_rw [comp_apply] at hs
    rw [hs]
    rw [ha]

NewTheorem congr_fun
