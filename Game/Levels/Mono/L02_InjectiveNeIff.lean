import Game.Levels.Mono.L01_Injective

World "Mono"
Level 2

Title ""

-- Introduction ""
Introduction "Intro Mono L02"

open Function

Statement (f : ℤ → ℤ  ) (hf : Injective f): f 1 ≠ f (-1) := by
  /-
  Hint "**Robo**: Hier kannst du abkürzen, indem du statt der Definition von `Injective f` die äquivalente Beschreibung `a ≠ b → f a ≠ f b` von Injektivität benutzt.
  In Leansch ist das Teil von `Injective.ne_iff`:  für injektive Abbildungen gilt `f a ≠ f b ↔ a ≠ b`."
  -/
  Hint "Use short cut by instead of the definition of `Injective f` using equivalent description
  `a ≠ b → f a ≠ f b`. In Leanic it is part of `Injective.ne_iff`. For injective mapping it holds
  that `f a ≠ f b ↔ a ≠ b`"
  rw [Injective.ne_iff]
  -- Hint (hidden := true) "**Robo**: `decide`?"
  Hint (hidden := true) "Perhaps, try using `decide` here"
  decide
  assumption

/---/
TheoremDoc Function.Injective.ne_iff as "Injective.ne_iff" in "Function"
NewTheorem Function.Injective.ne_iff
