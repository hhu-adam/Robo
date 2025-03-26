import Game.Metadata
import Game.Levels.Babylon.L07_Induction2_sum_insert2

World "Babylon"
Level 8

open Finset
open Robo.NN.Finset -- temporary solution to make correct version of `insert_Icc_eq_Icc_add_one_right` available

-- open BigOperators

Title ""

Introduction
"
Aus reiner Neugierde schaust du dir noch einen Nachbarsturm näher a.
"

Statement (n : ℕ) : (∑ i ∈ Icc 0 n, (2 * i + 1)) = (n + 1)^ 2 := by
  Hint "
    **Du**:  Hier also eine Summe nur über ungeraden Zahlen.
    $$
    \\sum_\{i = 0}^n (2i + 1) = n^2
    $$

    **Robo**: Das funktioniert doch genau gleich wie zuvor.
    "
  induction n with d hd
  · simp
  · rw [← insert_Icc_eq_Icc_add_one_right]
    · rw [sum_insert]
      · rw [hd]
        ring
      · simp
    · linarith

TheoremTab "∑ Π"

Conclusion "
  **Babylonier**:  Und?  Gefällt es euch hier?

  **Robo**:  Ja, sehr.  Das ist wirklich alles beeindruckend, was ihr hier aufgebaut habt.
  Aber wir wollen euch nicht länger aufhalten.

  **Du**:  Ich denke auch, wir sollten langsam wieder aufbrechen.

  Ihr verabschiedet euch und macht euch auf den Weg zurück zum Raumschiff.
"
