import Game.Metadata

World "Contradiction"
Level 1

Title "Was wir haben, haben wir."

Introduction
"
**Benedictus**: Hier, schaut mal. Das habe ich für Euch vorbereitet.
"

Statement (A B : Prop) (h : A → ¬ B) (k : A ∧ B) : False := by
  Hint "**Du**: Also als erstes teile ich wohl mal das Und (`∧`) auf."
  rcases k with ⟨h₁, h₂⟩
  Hint (strict := true) "
    **Du**: Und jetzt …

    **Benedictus**: … solltest du dir ein passendes Zwischenresultat zurechtlegen.

    **Robo**: Ja! Probier mal `have g : ¬ B`!"
  have g : ¬ B
  · Hint "
      **Du**: Was? Jetzt hab ich einfach angenommen, dass sei richtig?

      **Robo**: Nee, jetzt musst du das erst noch beweisen, bevor du es dann benutzen kannst."
    Hint (hidden := true) "**Robo**: `apply` sollte helfen"
    apply h
    assumption
  Hint "**Du**: Und wie war das nochmals wenn zwei Annahmen sich widersprechen?

  **Robo**: `contradiction`."
  contradiction

Conclusion "**Benedictus**: Das sieht gut aus!"

NewTactic «have»
DisabledTactic «suffices»
