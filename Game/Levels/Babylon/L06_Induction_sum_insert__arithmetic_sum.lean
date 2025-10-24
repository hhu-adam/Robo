import Game.Metadata


World "Babylon"
Level 6

Title "" -- "Arithmetische Summe"

/-
Introduction
"
**Babylonier**: Kommt, ich zeig euch mal einen unserer schönsten Türme!

Der Weg führt steil bergan.  Der Turm, der euch oben auf dem Berg erwartet, ist tatsächlich sehr imposant.

**Robo**: Das muss der bekannte *Gaußsche Turm von Babylon* sein!
Über den hab ich schon einmal etwas gelesen.

**Babylonier**: Richtig. Gauß war ein Babylonier!
"
-/

Introduction "`INTRO` Intro Babylon L06"

open Finset

/---/
TheoremDoc arithmetic_sum as "arithmetic_sum" in "∑ Π"

-- This would also easily work as a sum in ℚ,
-- and BOSS level would even be easier to prove in ℚ,
-- but cannot get initial conversion to ℚ to work!

Statement arithmetic_sum (n : ℕ) :
     (∑ i ∈ Icc 0 n , i : ℚ) = 1/2  * n * (n + 1) := by
  /-
  Hint "**Du**: Diese Summe habe ich auch schon einmal gesehen.
    $$
    \\sum_\{i = 0}^n i = \\tfrac\{1}\{2} \\cdot n \\cdot (n + 1)
    $$

  Gabs da nicht diese Geschichte mit dem kleinem Gauß, der da ein ganz einfaches Argument für hatte?

  **Robo**: Mit Geschichte kenn ich mich nicht aus.  Ich würde einfach eine Induktion über `n` machen.
  Das wäre auf Leansch: `induction n with d hd`!

  **Du**:  Warum `with …`?

  **Robo**:  Der Zusatz ist natürlich optional.
  Du kannst damit Namen für Induktionsvariable (`d`) und -hypothese (`hd`) vorgeben."
  -/
  Hint "Try `induction n with d hd`"
  induction n with d hd
  /-
  Hint "**Du**: Zuerst der Induktionsanfang …

  **Robo**: Diesen kannst du oft mit `simp` abkürzen!"
  -/
  Hint "Try `simp`"
  simp
  /-
  Hint "**Robo**: Jetzt willst du das Interval $[0, {d}+1]$, über das summiert wird, aufspalten in $[0,{d}]$ und ${d}+1$.
    Dazu könntest du das Lemma `insert_Icc_eq_Icc_add_one_right` verwenden, das wir schon gesehen hatten.
  "
  -/
  Hint "Try `insert_Icc_eq_Icc_add_one_right`"
  rw [← insert_Icc_eq_Icc_add_one_right]
  /-
  Hint "**Robo**:  Genau!  Und jetzt spaltet dir `sum_insert` die Summe genau so auf, wie du das haben möchtest:
  also eine Summe über $[0,{d}]$ und dann noch einen zusätzlichen Summanden für ${d}+1$.
  Probiers mal: `rw [sum_insert]`
  "
  -/
  Hint "Try `rw [sum_insert]`"
  rw [sum_insert]
  /-
  Hint (hidden := true)
  "**Du**: Und wie wende ich jetzt die Induktionshypothese an?

  **Robo**: Mit `rw`, wie jede andere Annahme auch."
  -/
  Hint (hidden := true) "Try `rw`"
  rw [hd]
  /-
  Hint "
    **Du**: Der Rest sollte jetzt einfach nur Rechnerei sein.

    **Robo**:  Stimmt.  Irgendeine Kombination von `simp` und `ring` sollte das schaffen.
  "
  -/
  Hint "Try `simp` & `ring`"
  simp
  ring
  simp
  linarith

NewTactic induction

/---/
TheoremDoc Finset.sum_insert as "sum_insert" in "∑ Π"
NewTheorem Finset.sum_insert

-- Nat.zero_eq
-- Nat.succ_eq_add_one
-- Fin.sum_univ_castSucc

TheoremTab "∑ Π"

Conclusion "Conclusion Babylon L06"
