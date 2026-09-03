import Game.Metadata
import Game.Levels.MatrixSpan.L08
import Game.Levels.Robotswana

World "Span"
Level 9

Introduction "Intro Span L09"

open Real Function Set Finset BigOperators Matrix

Statement {n : ℕ} (A : Mat[n+2,n+2][ℝ]) :
    Submodule.span ℝ (Submonoid.powers A).carrier ≠ ⊤ := by
  Hint "[Hint sp9bycn] The goal is a negation, so assume the span really is everything and
    hunt for a contradiction."
  intro hspan
  /- Here we could use `⟨n + 1, by grind⟩` instead of `⟨n + 1, (n + 1).lt_add_one⟩`. -/
  Hint (strict := true) "[Hint sp9matu] If the span is all of the matrices, then in particular
    the two matrix units `E 0 (n + 1)` and `E (n + 1) 0` belong to it. Record them with `have`."
  Hint (hidden := true) (strict := true) "[Hint sp9haE1] Establish the condition
    `E 0 ⟨n + 1, (n + 1).lt_add_one⟩ ∈ Submodule.span ℝ (Submonoid.powers A).carrier` by `have`."
  have h₁ : E 0 ⟨n + 1, (n + 1).lt_add_one⟩ ∈ Submodule.span ℝ (Submonoid.powers A).carrier := by
    rw [hspan]
    simp
  Hint (hidden := true) (strict := true) "[Hint sp9haE2] Establish the condition
    `E ⟨n + 1, (n + 1).lt_add_one⟩ 0 ∈ Submodule.span ℝ (Submonoid.powers A).carrier` by `have`."
  have h₂ : E ⟨n + 1, (n + 1).lt_add_one⟩ 0 ∈ Submodule.span ℝ (Submonoid.powers A).carrier := by
    rw [hspan]
    simp
  Hint (strict := true) "[Hint sp9pspc] Any two elements of the span commute — that is
    `powers_span_commute`. Feed it `{h₁}` and `{h₂}`."
  obtain h₃ := powers_span_commute h₁ h₂
  Hint (strict := true) "[Hint sp9mlsm] A product of matrix units collapses:
    `E i j * E j k = E i k`. This is the theorem `E.mul_same`."
  Hint (strict := true) (hidden := true) "[Hint sp9rwh3] Rewrite it at `{h₃}`."
  rw [E.mul_same, E.mul_same] at h₃
  Hint (strict := true) "[Hint sp9entr] But `E 0 0` carries a `1` at the entry `(0, 0)` while
    `E (n + 1) (n + 1)` carries a `0` there, so `{h₃}` cannot hold. Compare the two matrices
    entrywise."
  Hint (hidden := true) (strict := true) "[Hint sp9cgf2] Use `congr_fun₂` to read off the
    entry `(0, 0)`."
  obtain eq_aux := congr_fun₂ h₃ 0 0
  simp [E] at eq_aux

/--
Let `f g` be a function of type `α → β → γ`, with assumption `h : f = g`,
and let `x : α`, `y : β` then `f x y = g x y`. This can be obtained by
`congr_fun₂ h x y`.
-/
TheoremDoc congr_fun₂ as "congr_fun₂" in "Function"

NewTheorem congr_fun₂
