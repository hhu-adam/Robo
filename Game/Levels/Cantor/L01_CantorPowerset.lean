import Game.Metadata
import Game.Levels.Cantor.L00_CantorPowerset

World "Cantor"
Level 2

Title "Cantor's Diagonalargument"

Introduction
"
**Cantor**: Also und jetzt die eigentliche Aussage!
"

Conclusion "**Du**: Uff. Aber ehrlich habe ich die das \"Diagonale\" daran noch nicht
ganz gesehen.


**Cantor**: Natürlich, das kann ich euch zeigen, aber da muss ich etwas ausholen…
"

open Set Function

Statement {A : Type*} (f : A → Set A) :
    ¬ Surjective f := by
  Hint (hidden := true) "**Du**: Also ein Widerspruchsbeweis?"
  by_contra hf
  -- Branch
  --   Hint (strict := true)
  --   "**Du**: Und jetzt existiert durch Surjektivität ein Urbild von `TODO`.

  --   **Cantor**: Genau! Und dann überlegt euch, ob `b ∈ f b` ist oder nicht für
  --   dieses Urbild `b`!"
  --   have hsurj := hf { a | a ∉ f a }
  --   rcases hsurj with ⟨b, hb⟩
  --   Hint (hidden := true) "**Robo**: Das machen wir glaubs am besten mit `by_cases`."
  --   by_cases b ∈ f b
  --   · Branch
  --       clear hf hb
  --       Hint "**Du**: Jetzt will ich ja auch noch `{b} ∉ {f} {b}` zeigen für den Widerspruch.

  --       **Robo**: Dann sag doch `suffices hn : {b} ∉ {f} {b}`, erinnerst du dich?"
  --     suffices hn : b ∉ f b
  --     · contradiction
  --     rw [hb]
  --     rw [mem_setOf]
  --     simp
  --     assumption
  --   · Hint "**Robo**: Und noch den Fall wenn `{b} ∉ {f} {b}`"
  --     suffices hn : b ∈ f b
  --     · contradiction
  --     rw [hb]
  --     rw [mem_setOf]
  --     assumption
  Branch
    apply cantor_helper
    -- BUG: This does not trigger
    Hint "**Robo**: als Erinnerung: Wenn du so etwas wie `?f` siehst, bedeutet das, dass
    noch nicht spezifiziert wurde welche Funktion benützt wird. Du hättest besser
    `apply cantor_helper f` geschrieben. Aber du kannst auch einfach mal weitermachen, als ob `?f`
    schon `{f}` wäre, und vermutlich wird Lean das irgendwann automatisch einfüllen."
  Hint "**Cantor**: Wendet doch gleich das Resultat von vorhin an!

  **Robo**: Ich hab das als `cantor_helper f` gespeichert."
  apply cantor_helper f
  rcases hf { x | x ∉ f x } with ⟨w, hw⟩
  use w

NewHiddenTactic unfold_let -- TODO: remove
TheoremTab "Function"
