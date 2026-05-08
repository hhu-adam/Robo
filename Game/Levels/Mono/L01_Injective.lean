import Game.Metadata


World "Mono"
Level 1

Title ""

/-
Introduction
"
Ganz oben sind tatsächlich wieder viele Formalosophen versammelt.
Sie heißen euch freudig willkommen, und kommen dann gleich zur Sache.
"
-/
Introduction "Intro Mono L01"

open Set Function

Statement :
    let f := fun (n : ℤ) ↦ n + 3
    Injective f := by
  /-
  Hint "
    **Robo**: `Injective` ist so definiert, wie du es erwarten würdest: `∀ \{a b : U}, f a = f b → a = b`.
    Du kannst das wieder leicht mit `unfold` prüfen, wenn du mir nicht traust."
  -/
  Hint "`Injective` is defined as `∀ \{a b : U}, f a = f b → a = b`. You can check this with `unfold`"
  /-
  Hint (hidden := true) "
    **Robo**:  Fang doch mit `intro a b` an.
  "
  -/
  Hint (hidden := true) "Try starting with `intro a b`"
  Branch
    unfold Injective
  intro a b
  Branch
    simp [f]
  intro ha
  /-
  Hint (hidden := true)
  "**Robo**: Ich glaube, du solltest jetzt mit der Definition von `{f}` die
  Annahme `{ha}` vereinfachen."
  -/
  Hint (hidden := true) "Use `{f}` to simplify assumption `{ha}`"
  simp [f] at ha
  assumption

NewDefinition Function.Injective
TheoremTab "Function"

-- Conclusion "Das habt ihr gut gemacht, finden die Formalosophen."
Conclusion "Conclusion Mono L01"
