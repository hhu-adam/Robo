import Game.Metadata

World "Babylon"
Level 3

Title ""

Introduction
"Als nächstes kommt ihr an einen leeren Bauplatz, auf dem sich schon lange nichts getan zu haben scheint.
Auf dem Bauschild steht:"

open Finset

Statement (I : Finset ℤ) (h : ∀ i ∈ I, (i-1)*i*(i+1) = 0): ∑ i ∈ I, (i-1)*i*(i+1)  = 0  := by
  Hint "
    **Du**: Die Annahme sieht wie eine verklausulierte Variante von $I \\subseteq \\\{-1,0,1\\}$ aus.
    Das kann ja so oder so keine große Summe werden.

    **Robo**: Nein.  Aber wir brauchen wohl einen Zwischenschritt, um das angegebene Ergebnis zu erhalten.
    Ich schlage vor: `trans ∑ i ∈ I, 0`.  Das Summezeichen schreibst du als `\\sum`.
    "
  trans ∑ i ∈ I, 0
  Hint "
    **Robo**:  Genau. Jetzt kannst du nämlich `apply sum_congr` schreiben
    – zwei Summen sind insbesondere dann gleich, wenn über dieselbe Indexmenge summiert wird und
      auch die Ausdrücke, über die summiert wird, übereinstimmen.
  "
  apply sum_congr
  rfl
  assumption
  simp

/---/
TheoremDoc Finset.sum_congr as "sum_congr" in "∑ Π"
NewTheorem Finset.sum_congr

TheoremTab "∑ Π"

NewDefinition Sum
