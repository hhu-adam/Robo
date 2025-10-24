import Game.Metadata
import Game.Levels.Babylon.L06_Induction_sum_insert__arithmetic_sum

World "Babylon"
Level 7

Title ""

/-
Introduction
"Direkt neben dem Gaußschen Turm ist wieder ein leerer Bauplatz.  Diesmal steht folgendes auf dem Schild:"
-/
Introduction "`INTRO` Intro Babylon L07"

open Finset

Statement  (n : ℕ) : ∑ i ∈ Icc (-n : ℤ) n, i = 0 := by
    /-
    Hint "
      **Du**:  $\\sum_\{i=-n}^{n} i = 0$ – ja, das sieht richtig aus.

      **Robo**:  Sollte auch ganz genau so beweisbar sein, wie die Gaußsche Summe eben …
      außer dass du vermutlich nach `insert_Icc_eq_Icc_add_one_right` auch noch
      `insert_Icc_eq_Icc_sub_one_left` brauchen wirst.
    "
    -/
    Hint "Try `insert_Icc_eq_Icc_add_one_right`, `insert_Icc_eq_Icc_sub_one_left`"
    induction n with d hd
    · simp
    · simp
      rw [← insert_Icc_eq_Icc_add_one_right]
      /-
      Hint (hidden := true) "
        **Robo**:  Genau, und jetzt wieder `rw [sum_insert]`.
        "
      -/
      Hint (hidden := true) "`rw [sum_insert]`"
      · rw [sum_insert]
        /-
        Hint "
          **Robo**: Ich fürchte, als nächstes musst du `-1 + -{d}` als `-{d} - 1` umschreiben.
          Vielleicht ist es am einfachsten, wenn du diese Gleichung mit `have` ausformulierst.
          Du musst nur irgendwie klarmachen, dass das eine Gleichung in `ℤ` sein soll,
          beispielsweise so:
          ```
          have : -1 + (-d : ℤ)  = -d - 1
          ```
        "
        -/
        Hint "Try `have : -1 + (-d : ℤ)  = -d - 1`"
        · --have : (-1 : ℤ)  + -↑d  = -↑d - 1 := by
          have : -1 + (-d : ℤ)  = -d - 1 := by
            ring
          rw [this]
          rw [← insert_Icc_eq_Icc_sub_one_left]
          · rw [sum_insert]
            · rw [hd]
              ring
            · simp
          · --omega -- fails; omega appears to treat ↑d as a random integer rather than a natural number
            linarith
        · simp
      · linarith

TheoremTab "∑ Π"

Conclusion "Conclusion Babylon L07"
#min_imports
