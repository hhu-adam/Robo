import Game.Levels.Mono.L01_Injective

World "Mono"
Level 2

Title "" -- ""

Introduction ""

open Function

Statement (f : ℤ → ℤ  ) (hf : Injective f): f 1 ≠ f (-1) := by
  Hint "**Robo**: Hier kannst du abkürzen, indem du statt der Definition von `Injective f` die äquivalente Beschreibung `a ≠ b → f a ≠ f b` von Injektivität benutzt.
  In Leansch ist das Teil von `Injective.ne_iff`:  für injektive Abbildungen gilt `f a ≠ f b ↔ a ≠ b`."
  rw [Injective.ne_iff]
  Hint (hidden := true) "**Robo**: `decide`?"
  decide
  assumption

/---/
TheoremDoc Function.Injective.ne_iff as "Injective.ne_iff" in "Function"
NewTheorem Function.Injective.ne_iff
