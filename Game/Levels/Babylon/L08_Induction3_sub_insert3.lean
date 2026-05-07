import Game.Metadata
import Game.Levels.Babylon.L07_Induction2_sum_insert2

World "Babylon"
Level 8

open Finset

-- open BigOperators

Title ""

/-
Introduction
"
Aus reiner Neugierde schaust du dir noch einen Nachbarsturm näher an.
"
-/
Introduction "Intro Babylon L08"
-- attribute [game_simp] Icc_self sum_singleton mul_zero zero_add one_pow mem_Icc zero_le add_le_iff_nonpos_right nonpos_iff_eq_zero one_ne_zero and_false not_false_eq_true

Statement (n : ℕ) : (∑ i ∈ Icc 0 n, (2 * i + 1)) = (n + 1)^ 2 := by
  /-
  Hint "
    **Du**:  Hier also eine Summe nur über ungeraden Zahlen.
    $$
    \\sum_\{i = 0}^n (2i + 1) = n^2
    $$

    **Robo**: Das funktioniert doch genau gleich wie zuvor.
    "
  -/
  Hint "Try solving $$ \\sum_\{i = 0}^n (2i + 1) = n^2 $$ by induction"
  induction n with d hd
  · simp
  · rw [← insert_Icc_right_eq_Icc_add_one]
    · rw [sum_insert]
      · rw [hd]
        ring
      · simp
    · linarith

TheoremTab "∑ Π"

/-
Conclusion "
  **Babylonier**:  Und?  Gefällt es euch hier?

  **Robo**:  Ja, sehr.  Das ist wirklich alles beeindruckend, was ihr hier aufgebaut habt.
  Aber wir wollen euch nicht länger aufhalten.

  **Du**:  Ich denke auch, wir sollten langsam wieder aufbrechen.

  Ihr verabschiedet euch und macht euch auf den Weg zurück zum Raumschiff.
"
-/

Conclusion "Conclusion Babylon L08"
