import Game.Metadata

open Nat

World "Luna"
Level 6

Title ""

/-
Introduction
"**Ritha**:  Kann ich auch mal?  Hier."
-/
Introduction "`INTRO` Intro Luna L06"

open Finset

Statement {a b : ℤ} (h : a ≤ b + 1) :
  insert (b + 1) (Icc a b) = Icc a (b + 1) := by
  /-
  Hint "
    **Du**:  Was ist denn `Icc`?

    **Ritha**:  Na das **I**ntervall, das links **c**losed und rechts **c**losed, also abgeschlossen ist.

    **Robo**:  Du würdest `Icc a b` vermutlich als $[a, b]$ schreiben,
     oder als $\\\{a, a + 1, \\dots, b\\}$, weil wir ja hier wieder in den natürlichen Zahlen sind.
     Zu zeigen ist also:

     $$
     [a, b] ∪ \\\{ b + 1 \\} = [a, b + 1]
     $$
     "
  -/
  Hint "Remind that `Icc` is an interval which is closed to both sides. You could write `Icc a b`
  as $[a, b]$ or $\\\{a, a + 1, \\dots, b\\}$, because we are in the natual numbers. Therfore, the
  goal is: $$ [a, b] ∪ \\\{ b + 1 \\} = [a, b + 1] $$"
  -- Hint (hidden := true) "**Robo:** Gleichheit von Mengen ruft nach `ext`."
  Hint "Equality of sets demands `ext`"
  ext x
  /-
  Hint "
    **Robo:**  Schieß mal gleich noch ein `simp` hinterher.
  "
  -/
  Hint "Try `simp` afterwards"
  simp
  -- Hint "Ritha macht wieder irgendwelche Zeichen."
  Hint "`COMMENT` Ritha gives sighns to try omega"
  omega


TheoremTab "≤"
/---/
TheoremDoc Finset.insert_Icc_eq_Icc_add_one_right as "insert_Icc_eq_Icc_add_one_right" in "≤"
/---/
TheoremDoc Finset.insert_Icc_eq_Icc_sub_one_left as "insert_Icc_eq_Icc_sub_one_left" in "≤"
/---/
TheoremDoc Finset.insert_Icc_add_one_left_eq_Icc as "insert_Icc_add_one_left_eq_Icc" in "≤"
/---/
TheoremDoc Finset.insert_Icc_sub_one_right_eq_Icc as "insert_Icc_sub_one_right_eq_Icc" in "≤"

NewTheorem
Finset.insert_Icc_eq_Icc_add_one_right
Finset.insert_Icc_eq_Icc_sub_one_left
Finset.insert_Icc_add_one_left_eq_Icc
Finset.insert_Icc_sub_one_right_eq_Icc

NewDefinition Finset.Icc

Conclusion ""
