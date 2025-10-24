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
Introduction "`INTRO` Intro Piazza L04"

namespace Set

#check  (univ : Set ℕ)

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
  Hint "Explain differnece between `univ` and `ℕ`. Try `rw [eq_univ_iff_forall]`"
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
  -- Hint "
  --  **Robo**: Und jetzt `simp`.  Du hättest sogar direkt `simp [eq_univ_iff_forall]` nehmen können.
  --  "
  Hint "Try `simp` | `simp [eq_univ_iff_forall]`"
  simp?
  intro x
  /-
  Hint "
    **Du**: Und jetzt `by_cases h : Even n`?

    **Robo**: Ja, das würde zum Ziel führen.
    Aber eigentlich ist `Even x ∨ ¬Even x` ja eine Tautologie.
    Damit `tauto` sie erkennt, musst du sie nur entsprechend abstrahieren.
    Das ginge hier zum Beispiel mit:
    ```
    rw [← Nat.not_odd_iff_even]
    ```
    "
  -/
  Hint "Explain that `Even x ∨ ¬Even x` tautology. Try `rw [← Nat.not_odd_iff_even]`"
  Branch
    by_cases h : Even n
    left
    assumption
    right
    assumption
    done
  -- TODO: v4.22.0 update hat dies kaputt gemacht. Weiss nicht wieso
  -- Branch
  --   generalize h : (Even x) = A
  --   tauto
  rw [← Nat.not_odd_iff_even]
  tauto
  done

TheoremTab "Set"

NewTactic generalize
DisabledTactic ext

/---/
TheoremDoc Set.eq_univ_iff_forall as "eq_univ_iff_forall" in "Set"
NewTheorem Set.eq_univ_iff_forall

NewDefinition Set.univ

-- Conclusion ""
Conclusion "Conclusion Piazza L04"
