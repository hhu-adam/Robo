import Game.Metadata


World "Spinoza"
Level 2

Title "" -- "Es reicht!"

/-
Introduction
"
**Benedictus**: Ihr hättet natürlich auch erst das Hauptresultat und dann das
Zwischenresultat beweisen können. Das könnt Ihr ja mal an dieser Aufgabe probieren, die ist
ganz ähnlich.
"
-/
Introduction "`INTRO` Intro Spinoza L02"

Statement
    (A B : Prop) (h : A → ¬ B) (k₁ : A) (k₂ : B) : False := by
  /-
  Hint "
    **Robo**: Ich weiß was er meint! Anstatt `have` kannst du auch `suffices`
    verwenden. Das funktioniert genau gleich, außer, dass dann die beiden Beweisziele vertauscht sind.

    **Du**: Also nach `suffices g : ¬B` muss ich dann zuerst zeigen, wie man mit `g` den Beweis
    abschliesst, bevor ich `g` beweise?

    **Robo**: Genau!"
  -/
  Hint "Instead of `have`, `suffices` can be used. After `suffices g : ¬B`, you have to show how to
  prove goal by `g` before proving `g` itself."
  suffices g : ¬ B
  -- Hint "**Robo**: Also hier beendest du den Beweis unter der Annahme `{g}` sei wahr."
  Hint "End proof with assumption that `{g}` is true"
  contradiction
  -- Hint "**Robo**: Und hier beweist du das Zwischenresultat."
  Hint "`COMMENT` Prove intermediate result"
  apply h
  assumption

/-
Conclusion
"
**Benedictus**: Genau so meinte ich das. Ob Ihr nun in Zukunft `have` und
`suffices` verwendet, ist reine Geschmacksfrage. Hauptsache, Ihr wisst, wie Ihr
entfernte Ziele in kleinen Schritte erreicht.
"
-/
Conclusion "Conclusion Spinoza L02: The use of `have` or `suffices` is up to personal preference."

NewTactic «suffices»
DisabledTactic «have» tauto
