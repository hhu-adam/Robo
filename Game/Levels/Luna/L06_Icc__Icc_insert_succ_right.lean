import Game.Metadata

open Nat

World "Luna"
Level 6

Title ""

Introduction
"**Ritha**:  Kann ich auch mal?  Hier."

namespace Nat
open Finset
/---/
TheoremDoc Nat.Icc_insert_succ_right as "Icc_insert_succ_right" in "≤"

Statement Icc_insert_succ_right {a b : ℕ} (h : a ≤ b + 1) :
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

end Nat

TheoremTab "≤"

/---/
TheoremDoc Nat.Icc_insert_succ_left as "Icc_insert_succ_left" in "≤"
NewTheorem Nat.Icc_insert_succ_left


Conclusion ""
