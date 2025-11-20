import Game.Metadata

World "Spinoza"
Level 1

Title ""

/-
Introduction
"
**Benedictus**: Hier, schaut mal. Das habe ich für Euch vorbereitet.
"
-/
Introduction "`INTRO` Intro Spinoza L01"

Statement (A B : Prop) (h : A → ¬ B) (k : A ∧ B) : False := by
  -- Hint "**Du**: Also als erstes teile ich wohl mal das Und (`∧`) auf."
  Hint "Try to split `∧`"
  obtain ⟨h₁, h₂⟩ := k
  /-
  Hint (strict := true) "
    **Du**: Und jetzt …

    **Benedictus**: … solltest du dir ein passendes Zwischenresultat zurechtlegen.

    **Robo**: Ja! Probier mal wieder `have`.  Genauer: `have g : ¬ B`!"
  -/
  Hint (strict := true) "Try `have` in form of `have g : ¬ B`"
  have g : ¬ B
  /-
  · Hint "
      **Du**: Was? Jetzt hab ich einfach angenommen, dass sei richtig?

      **Robo**: Nein, jetzt musst du das natürlich erst noch beweisen, bevor du es dann benutzen kannst."
  -/
  · Hint "`COMMENT` Prove the assumption before using it"
    -- Hint (hidden := true) "**Robo**: `apply` sollte helfen"
    Hint (hidden := true) "`apply` should help"
    apply h
    assumption
  /-
  Hint "**Du**: Und wie war das nochmals wenn zwei Annahmen sich widersprechen?

  **Robo**: `contradiction`."
  -/
  Hint "If to assumptions contradict each other use `contradiction`"
  contradiction

-- Conclusion "**Benedictus**: Das sieht gut aus!"
Conclusion "`CONC` Conclusion Spinoza L01"

--NewTactic «have»  -- now introduced very briefly in Implis
DisabledTactic «suffices» tauto
