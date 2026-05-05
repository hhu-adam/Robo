import Game.Metadata

World "Piazza"
Level 4

Title ""

/-
Introduction
"
  **Sub:** Ich habe auch schon etwas gelernt:
"
-/
Introduction "Intro Piazza L04"

open Nat
namespace Set

#check  (univ : Set ℕ)
attribute [game_simp] mem_union mem_setOf_eq

Statement : { n : ℕ | Even n} ∪ { n : ℕ | Odd n} = univ := by
  /-
  Hint "
    **Du**:  Was ist denn `univ`?

    **Robo**:  `univ` ist die maximale Teilmenge:  alle natürlichen Zahlen.

    **Du**:  Also einfach `ℕ`?

    **Robo**:  Jein. `univ : Set ℕ` ist “ganz ℕ”, aber aufgefasst als *Teilmenge* von `ℕ`.

    Ext, Fin, Set, Sub und Mem sehen euch groß an.

    **Set**:  Das kann man doch gar nicht verwechseln!  Hier *ist* eine Blaubeere,
    das hier ist der *Korb mit allen Blaubeeren*, und die Beere *liegt in* diesem Korb.

    **Mem**:  Und genauso *ist* 5 eine natürlich Zahl (`5 : ℕ`),
     `univ : Set ℕ` ist die *Menge aller natürlicher Zahlen*, und `5` *liegt in* dieser Menge (`5 ∈ univ`).
     Was ist daran verwirrend?

    **Robo** (*zu dir*):  Zerbrich dir nicht den Kopf darüber.
    Ich schlage vor, du fängst hier einfach mal mit `rw [eq_univ_iff_forall]` an,
    dann siehst du genau, was gefragt ist.
    "
  -/
  Hint "Explain `univ`: `univ` is interpreted as `ℕ` but as a subset of it self i.e. `univ : Set ℕ`
  is subset of `ℕ`. So, as 5 is a natural number (`5 : ℕ`) and it holds that `univ : Set ℕ`, `5`
  is also in this set i.e. `5 ∈ univ`. Try `rw [eq_univ_iff_forall]`"
  /-
  `ext` also works, but WANT to introduce
  `eq_univ_iff_forall` [and `generalize` -- no longer needed] here!
  So `ext` is disabled.
  -/
  /-
  Branch
    ext
    simp
  -/
  rw [eq_univ_iff_forall]
  Hint "Try via `simp` or directly `simp [eq_univ_iff_forall]`"
  simp
  intro n
  Hint "One option: `by_cases h : Even {n}`.
  But in any case, will need `not_odd_iff_even`
  (or `not_even_iff_odd`) at some point,
  so might as well start with it
  and obtain tautology `¬Odd «{n}» ∨ Odd «{n}»`."
  Branch
    by_cases h : Even n
    left
    assumption
    right
    rw [← not_even_iff_odd]
    assumption
  Branch
    rw [← not_even_iff_odd]
    Hint (hidden := true) "[Piazza] `tauto`"
    /- No, first `generalize`:
    ```
    generalize h : (Even {n}) = A
    ```
    generalize h : (Even n) = A
    -/
    tauto
  rw [← not_odd_iff_even]
  Hint (hidden := true) "[Piazza] `tauto`"
  /- No, first `generalize`:
  ```
  generalize h : (Odd {n}) = A
  ```"
  generalize h : (Odd n) = A
  -/
  tauto

TheoremTab "Set"

--NewTactic generalize
DisabledTactic ext

/---/
TheoremDoc Set.eq_univ_iff_forall as "eq_univ_iff_forall" in "Set"
NewTheorem Set.eq_univ_iff_forall

NewDefinition Set.univ

Conclusion ""
