import Game.Metadata

World "Piazza"
Level 4

Title ""

Introduction
"
  **Sub:** Ich habe auch schon etwas gelernt:
"
namespace Set

#check  (univ : Set ℕ)

Statement : { n : ℕ | Even n} ∪ { n : ℕ | Odd n} = univ := by
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
  /-
  `ext` also works, but WANT to introduce
  `eq_univ_iff_forall` and `generalize` here!
  So `ext` is disabled
  -/
  /-
  Branch
    ext
    simp
  -/
  rw [eq_univ_iff_forall]
  Hint "
    **Robo**: Und jetzt `simp`.  Du hättest sogar direkt `simp [eq_univ_iff_forall]` nehmen können.
    "
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
