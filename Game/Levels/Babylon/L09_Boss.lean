import Game.Metadata

import Game.Levels.Babylon.L08_Induction3_sub_insert3

World "Babylon"
Level 9
Title ""

/-
Introduction
"
Ihr seid noch nicht weit gegangen, da kommt hinter einem Turm plötzlich ein besonders großer Babylonier hervor,
stellt sich euch in den Weg, schaut euch finster an und fordert in tiefer Stimme einen Beweis der
folgenden Gleichung.
"
-/
Introduction "`INTRO` Intro Babylon L09"

open Finset

-- open BigOperators


Statement (m : ℕ) : (∑ i ∈ Icc 0 m, (i : ℚ) ^3) = (∑ i ∈  Icc 0 m, i : ℚ)^2 := by
  /- Hint "**Du**: Naja. Das wird schon klappen … " -/
  Hint "Comment"
  induction m with n n_ih
  · simp
  · rw [← insert_Icc_eq_Icc_add_one_right]
    · rw [sum_insert]
      · simp
        rw [n_ih]
        /-
        Hint (hidden := true) "
          **Robo**:  Denk daran, dass wir schon `arithmetic_sum` bewiesen hatten.
        "
        -/
        Hint (hidden := true) "Try `arithmetic_sum`"
        rw [arithmetic_sum]
        simp
        ring
      · simp
    · linarith

TheoremTab "∑ Π"

/-
Conclusion "Der Babylonier denkt ganz lange nach, und ihr bekommt das Gefühl, dass er gar nie
aggressiv war, sondern nur eine sehr tiefe Stimme hat.

Mit einem kleinen Erdbeben setzt er sich hin und winkt euch dankend zu."
-/
Conclusion "`CONC` Conclusion Babylon L09"
