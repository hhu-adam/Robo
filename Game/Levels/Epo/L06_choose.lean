import Game.Metadata


World "Epo"
Level 6

Title "" -- "Every function with nonempty fibres has a right inverse."


/- Introduction "" -/
Introduction "Intro Epo L06"

open Function

Statement {A B : Type} (f : A → B) (nonempty_fibre : ∀ b : B, ∃ (x : A), f x = b) :
    HasRightInverse f := by
  /-
  Hint "**Du**:  Das riecht irgendwie nach Auswahlaxiom.

  **Robo**:  Bingo.  Erinnerst du dich noch an `choose`?
  Hier kommt `choose` so richtig in sein Element.
  Probier mal `choose g hg using nonempty_fibre`."
  -/
  Hint "Try `choose g hg using nonempty_fibre`"
  choose g hg using nonempty_fibre
  use g
  assumption

-- NewTactic choose  -- wird nun bereits in Quantus eingeführt
