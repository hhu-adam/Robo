import Game.Metadata

World "Implis"
Level 10

Title "" -- "Genau dann wenn"

/-
Introduction
"
**Operationsleiter**: Das hier ist wieder für meinen beschränkten Kollegen. Ich glaube,
`rw` mag der auch nicht. Geht das trotzdem?
"
-/
Introduction "Intro Implis L10: `rw` is not allowed here as well"

Statement (A B C : Prop) (h : A ↔ B) (g : B → C) : A → C := by
  /-
  Hint "
    **Du**: Naja ich kann wohl immerhin mal mit `intro` anfangen …

    **Robo**: … und dann schauen wir weiter!"
  -/
  Hint "Try `intro`"
  intro hA
  /-
  Hint "
    **Robo**: Also eine Implikation wendet man mit `apply` an …

    **Du**: Weiß ich doch! Aber `{h}` ist keine Implikation, sondern eine Äquivalenz.
    Da würde ich doch eigentlich `rw [← {h}]` sagen wollen.

    **Robo**: Die Richtung `{A} → {B}` von `{h}` heißt `{h}.mp`. Du kannst sie
    mit `apply ({h}.mp) at …` anwenden."
  -/
  Hint "Try `apply ({h}.mp) at …`"
  Branch
    apply g
    -- Hint "**Robo**: So kannst Du natürlich auch anfangen."
    Hint "Story"
    apply h.mp
    assumption
  apply h.mp at hA
  apply g at hA
  assumption

/-
Conclusion "
**Operationsleiter**: Okay, super. Das müsste passen.

Er telefoniert wieder.

**Operationsleiter**: Bingo!
"
-/
Conclusion "`CONC` Conclusion Implis L10"

DisabledTactic tauto rw
