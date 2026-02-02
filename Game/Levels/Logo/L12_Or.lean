import Game.Metadata

World "Logo"
Level 12

Title "" -- "Oder"

/-
Introduction
"
Der nächste bitte …
"
-/
Introduction "Intro Logo L12"

Statement (A B : Prop) (hA : A) : A ∨ (¬ B) := by
  /-
  Hint "
    **Du** Muss ich jetzt wieder das Beweisziel de-konstruieren?

    **Robo** Nein, viel einfacher. Wenn du eine Oder-Aussage beweisen sollst, musst du dich
    einfach entscheiden, ob du die linke oder rechte Seite beweisen willst.

    **Du** Und wie erkläre ich meinem Formalosophen, welche Seite ich gern beweisen würde?
    Ich will natürlich `{A}` beweisen!

    **Robo** Mit `left` bzw. `right`. Ist doch logisch, oder?"
  -/
  Hint "Try to proof `{A}` by using `left` | `right`"
  Branch
    right
    -- Hint "**Robo** Wusste gar nicht, dass du eine Links-Rechts-Schwäche hast. Probier's nochmal."
    Hint "Try Right tactic"
  left
  assumption

/-
Conclusion
"
Auch dieser Formalosoph zieht zufrieden von dannen.
"
-/
Conclusion "Conclusion Logo L12"

NewDefinition Or
NewTactic left right
DisabledTactic tauto
