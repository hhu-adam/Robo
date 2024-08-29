import Game.Metadata

World "Implication"
Level 10

Title "Genau dann wenn"

Introduction
"
**Operationsleiter**: Das hier ist wieder für meinen beschränkten Kollegen. Ich glaube,
`rw` mag der auch nicht. Geht das trotzdem?
"

Statement (A B C : Prop) (h : A ↔ B) (g : B → C) : A → C := by
  Hint "
    **Du**: Naja ich kann wohl immerhin mal mit `intro` anfangen …

    **Robo**: … und dann schauen wir weiter!"
  intro hA
  Hint "
    **Robo**: Also eine Implikation wendet man mit `apply` an …

    **Du**: Weiß ich doch! Aber `{h}` ist keine Implikation, sondern eine Äquivalenz.
    Da würde ich doch eigentlich `rw [← {h}]` sagen wollen.

    **Robo**: Die Richtung `{A} → {B}` von `{h}` heißt `{h}.mp`. Du kannst sie
    mit `apply ({h}.mp) at …` anwenden."
  Branch
    apply g
    Hint "**Robo**: So kannst Du natürlich auch anfangen."
    apply h.mp
    assumption
  apply h.mp at hA
  apply g at hA
  assumption

Conclusion "
**Operationsleiter**: Okay, super. Das müsste passen.

Er telefoniert wieder.

**Operationsleiter**: Bingo!
"

DisabledTactic tauto rw
