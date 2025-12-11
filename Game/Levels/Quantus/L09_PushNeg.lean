import Game.Metadata

World "Quantus"
Level 9

Title "" -- "PushNeg"

/-
Introduction
"
Nach langem Hin und Her haben sich die Formalosophinnen endlich auf folgende Frage geeignet.
"
-/
Introduction "Intro Quantus L09"

open Nat

Statement : ¬ ∃ (n : ℕ), ∀ (k : ℕ) , Odd (n + k) := by
  -- Hint "**Du**: Oha. Ganz links ein `¬`. Was du nicht sagst …"
  Hint "Remind about `¬`"
  Branch
    unfold Odd
    -- Hint "
    --  **Robo**: Dieser Lösungsweg scheint mir etwas zu schwierig.
    --  Ich würde nochmal zurückgehen und `Odd` behalten,
    --  damit man schlussendlich `not_odd_iff_even` brauchen kann!"
    Hint "Go back, keep `Odd` and try `not_odd_iff_even`"
  push_neg
  intro n
  Branch
    unfold Odd
    /-
    Hint "
      **Robo**: Dieser Lösungsweg scheint mir etwas zu schwierig.
      Ich würde nochmal zurückgehen und `Odd` behalten,
      damit man schlussendlich `not_odd_iff_even` brauchen kann!"
    -/
    Hint "Go back, keep `Odd` and try `not_odd_iff_even`"
  /-
  Hint "
    **Robo**: Jetzt brauchst du eine Zahl mit `use`, und danach vermutlich das
    Lemma `not_odd_iff_even` brauchen.

    **Du**: Könnte ich jetzt schon `not_odd_iff_even` anwenden?

    **Robo**: Nein, `rw` kann nicht innerhalb von Quantoren umschreiben.

    **Du**: Aber wie würde ich das machen?

    **Robo**: Zeig ich dir später, nicht hier vor großem Publikum.
    Ich würde jetzt lieber mit `use` eine richtige Zahl angeben, und danach umschreiben."
  -/
  Hint "Try `use` with a number and then `not_odd_iff_even`. You can not use `not_odd_iff_even`
  directly, as `rw` cannot be applied inside of quantors. Try `use` with a number."
  Branch
    use n + 2
    -- Hint "**Robo**: Gute Wahl! Jetzt kannst du `not_odd_iff_even` verwenden."
    Hint "Now you can apply `not_odd_iff_even`"
  Branch
    use n + 4
    -- Hint "**Robo**: Gute Wahl! Jetzt kannst du `not_odd_iff_even` verwenden."
    Hint "Now you can apply `not_odd_iff_even`"
  use n
  -- Hint "**Robo**: Gute Wahl! Jetzt kannst du `not_odd_iff_even` verwenden."
  Hint "Now you can apply `not_odd_iff_even`"
  rw [not_odd_iff_even]
  Branch
    tauto
  unfold Even
  use n

-- Note: The following two theorem are just added for completeness.

/-- In lieu of this theorem you can use `push_neg`. -/
TheoremDoc not_exists as "not_exists" in "Logic"
/-- Instead of this theorem you can use `push_neg`. `DOC2`-/
TheoremDoc Classical.not_forall as "not_forall" in "Logic"

NewTheorem not_exists Classical.not_forall

/-
Conclusion
"
Die Formalosophinnen sind ganz begeistert.
Nachdem sich der Beifall gelegt hat, hast du auch einmal eine Frage.

**Du**: Kann uns hier irgendjemand vielleicht ein bisschen Orientierung im Formaloversum geben?

**Alle**: Ja, ja.

**Du**: Wer denn?

Die Frage war wieder zu konkret. Betretenes Schweigen.
"
-/

Conclusion "Conclusion Quantus L09"
