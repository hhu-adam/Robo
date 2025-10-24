import Game.Metadata


open Nat

World "Luna"
Level 5

Title ""

/-
Introduction "
  **Lina:** Nochmal dieselbe Frage, aber jetzt in ℝ!
"
-/
Introduction "`INTRO` Intro Luna L05"

Statement (l m n x : ℝ) (h₁ : l ≤ m) (h₂ : m ≤ n) : l ≤ x ∧ x ≤ n → ¬ (m ≤ x ∧ x ≤ n) → x ≤ m := by
  /-
  Hint "
    **Du** (*zu Robo*):  Hier komme ich weder mit `omega` noch mit `linarith` weiter.

    **Robo**:  Ich glaube, du musst `linarith` nur etwas auf die Sprünge helfen.
    Lös am besten erst einmal ganz kanonisch die beiden Implikationen mit `intro` auf.
  "
  -/
  Hint "Try `intro`"
  intro hn hx
  /-
  Hint "
    **Robo**:  Und jetzt machst du die Annahme `{hx}` ein bisschen lesbarer.
    Probier vielleicht einmal `push_neg at {hx}`?
  "
  -/
  Hint "Try `push_neg at {hx}`"
  push_neg at hx
  /-
  Hint "
    **Robo**:  Mmm … `{hx} : m ≤ x → n < x` sieht immer noch suboptimal aus.
    Aber wir wissen ja, was `→` bedeutet – probier mal ein `rw` mit `imp_iff_or_not`!
  "
  -/
  Hint "Try `rw [imp_iff_or_not]`"
  --linarith (config := {splitNe := true, splitHypotheses := true}) -- fails
  rw [imp_iff_or_not] at hx
  /-
  Hint "
    **Robo**:  Okay.  Das ist besser. Und jetzt kannst du `{hx}` noch mit `obtain` in die
    beiden Bestandteile aufspalten.
  "
  -/
  Hint "Try `obtain hx | hx := hx`"
  --linarith (config := {splitNe := true, splitHypotheses := true}) -- fails
  obtain hx | hx := hx
  · linarith
  · linarith

TheoremTab "Logic"

-- Conclusion ""
Conclusion "Conclusion Luna L05"
