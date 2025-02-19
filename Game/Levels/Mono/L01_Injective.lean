import Game.Metadata


World "Mono"
Level 1

Title ""

Introduction
"
Ganz oben sind tatsächlich wieder viele Formalosophen versammelt.
Sie heißen euch freudig willkommen, und kommen dann gleich zur Sache.
"
open Set Function

Statement :
    let f := fun (n : ℤ) ↦ n + 3
    Injective f := by
  Hint "
    **Robo**: `Injective` ist so definiert, wie du es erwarten würdest: `∀ \{a b : U}, f a = f b → a = b`.
    Du kannst das wieder leicht mit `unfold` prüfen, wenn du mir nicht traust."
  Hint (hidden := true) "
    **Robo**:  Fang doch mit `intro a b` an.
  "
  Branch
    unfold Injective
  intro a b
  Branch
    simp [f]
  intro ha
  Hint (hidden := true)
  "**Robo**: Ich glaube, du solltest jetzt mit der Definition von `{f}` die
  Annahme `{ha}` vereinfachen."
  simp [f] at ha
  assumption

NewDefinition Function.Injective
TheoremTab "Function"

Conclusion "Das habt ihr gut gemacht, finden die Formalosophen."
