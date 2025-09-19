import Game.Metadata

open Nat

World "Luna"
Level 6

Title ""

Introduction
"**Ritha**:  Kann ich auch mal?  Hier."

open Finset

Statement {a b : ℤ} (h : a ≤ b + 1) :
  insert (b + 1) (Icc a b) = Icc a (b + 1) := by
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
  Hint (hidden := true) "**Robo:** Gleichheit von Mengen ruft nach `ext`."
  ext x
  Hint "
    **Robo:**  Schieß mal gleich noch ein `simp` hinterher.
  "
  simp
  Hint "Ritha macht wieder irgendwelche Zeichen."
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
