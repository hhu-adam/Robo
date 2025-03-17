import Game.Metadata

World "Piazza"
Level 2

Title ""

Introduction
"
  **Sub:** Ich habe auch schon etwas gelernt:
"
namespace Set

example : { n : ℕ | Even n} ∪ { n : ℕ | Odd n} = univ := by
  Hint "
    **Du**:  Was ist denn `univ`?

    **Robo**:  `univ` ist die maximale Teilmenge:  alle natürlichen Zahlen.

    **Du**:  Also einfach `ℕ`?

    **Robo**:  Jein. `univ : Set ℕ` ist “ganz ℕ”, aber aufgefasst als *Teilmenge* von `ℕ`.

    Fin, Set, Sub und Mem sehen ich euch groß an.

    **Set**:  Das kann man doch gar nicht verwechseln.  Ich kann sagen: das ist hier ist eine Blaubeere.
    Das hier ist der ganze Korb Blaubeeren.

    **Mem**:  Und genauso ist  `5 : ℕ`, aber `univ : Set ℕ`.  Das kann man doch gar nicht verwechseln!

    **Robo**:  Zerbrich dir nicht darüber den Kopf.
    Ich schlage vor, du fängst hier einfach mal mit `rw [eq_univ_iff_forall]` an,
    dann siehst du genau, was gefragt ist.
    "

  /- `ext` also works, but WANT to introduce
  `eq_univ_iff_forall` and `generalize` here!
  So `ext` is disabled    -/
  /- Branch --
    ext     Deshalb ist `ext` hier disabled.
    simp
  l-/
  rw [eq_univ_iff_forall]
  simp
  intro x
  Hint "
    **Du**: Und jetzt `by_cases h : Even n`?

    **Robo**: Ja, das würde zum Ziel führen.
    Aber eigentlich ist `Even x ∨ ¬Even x` ja eine Tautologie.
    Damit `tauto` sie erkennt, musst du sie nur entsprechend abstrahieren.
    Das ginge hier zum Beispiel mit:
    ```
    generalize h : (Even x) = A
    ```
    "
  /-Branch
    by_cases h : Even n
    left
    assumption
    right
    assumption
  -/
  generalize h : (Even x) = A
  tauto

TheoremTab "Set"

NewTactic generalize
DisabledTactic ext

/---/
TheoremDoc Set.eq_univ_iff_forall as "eq_univ_iff_forall" in "Set"
NewTheorem Set.eq_univ_iff_forall

NewDefinition Set.univ

Conclusion ""
