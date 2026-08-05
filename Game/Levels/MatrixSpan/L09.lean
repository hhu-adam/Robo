import Game.Metadata
import Game.Levels.MatrixSpan.L08
import Game.Levels.Robotswana

World "Span"
Level 9

Introduction "Intro Span L09"

open Real Function Set Finset BigOperators Matrix

Statement {n : ℕ} (A : Mat[n+2,n+2][ℝ]) :
    Submodule.span ℝ (Submonoid.powers A).carrier ≠ ⊤ := by
  Hint "[] Prove by contradiction."
  intro hspan
  /- Here we could use `⟨n + 1, by grind⟩` instead of `⟨n + 1, (n + 1).lt_add_one⟩`. -/
  Hint (strict := true) "[] Establish the condition
    `E 0 ⟨n + 1, (n + 1).lt_add_one⟩ ∈ Submodule.span ℝ (Submonoid.powers A).carrier` by `have`."
  have h₁ : E 0 ⟨n + 1, (n + 1).lt_add_one⟩ ∈ Submodule.span ℝ (Submonoid.powers A).carrier := by
    rw [hspan]
    simp
  Hint (hidden := true) (strict := true) "[] Establish the condition
    `E ⟨n + 1, (n + 1).lt_add_one⟩ 0 ∈ Submodule.span ℝ (Submonoid.powers A).carrier` by `have`."
  have h₂ : E ⟨n + 1, (n + 1).lt_add_one⟩ 0 ∈ Submodule.span ℝ (Submonoid.powers A).carrier := by
    rw [hspan]
    simp
  Hint (strict := true) "[] Remember the theorem `powers_span_commute`. Establish this using
    `{h₁}`, `{h₂}`."
  obtain h₃ := powers_span_commute h₁ h₂
  Hint (strict := true) "[] Note that `E i j * E j k = E i k`. This is the theorem `E.mul_same`."
  Hint (strict := true) (hidden := true) "[] Rewrite it at `{h₃}`."
  rw [E.mul_same, E.mul_same] at h₃
  Hint (strict := true) "[] Note that `E 0 0` is a matrix with `1` in the entry `(0, 0)` and `0` otherwise.
    And `E (n + 1) (n + 1)` is a matrix with `1` in the entry `(n + 1, n + 1)` and `0` otherwise. "
  Hint (hidden := true) (strict := true) "[] Using `congr_fun₂` to get the entry `(0, 0)`. "
  obtain eq_aux := congr_fun₂ h₃ 0 0
  simp [E] at eq_aux

/---/
TheoremDoc congr_fun₂ as "congr_fun₂" in "Function"

NewTheorem congr_fun₂

  -- part of old proof, broken.
  -- unfold single at this
  -- rw [if_neg] at this
  -- simp at *
  -- simp [Nat.succ_ne_zero]
  -- intro h
  -- norm_cast at h
  -- injection h
  -- simp at *
