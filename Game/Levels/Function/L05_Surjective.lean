import Game.Metadata

World "Function2"
Level 5

Title "Semiconjugate"
Introduction
"

"

open Function Nat

Statement {f : A → ℕ} {z : A} (h : f z = 0) {g : A → A}
    (hs : f ∘ g = succ ∘ f) : Surjective f := by
  intro n
  Hint "Induktion über `{n}`"
  induction n with n hn
  · use z
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
