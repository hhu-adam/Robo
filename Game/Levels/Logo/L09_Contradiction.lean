import Game.Metadata


World "Logo"
Level 9

Title "" -- "Aus Falschem folgt vieles."

/-
Introduction
"
Auftritt dritter Querulant.
"
-/
Introduction "`INTRO` Intro Logo L09"

/--  -/
Statement (n : ℕ) (h : n = 10) (g : n ≠ 10) : n = 42 := by
  /-
  Hint "
    **Du** Wieder ein Widerspruch in den Annahmen?

    **Robo**: Ich sehe, du hast langsam den Dreh raus."
  -/
  Hint "Try the Contradiction tactic"
  contradiction

/-
Conclusion
"
**Robo**: Gut gemacht. Bei dieser Frage ist auch ein bisschen offensichtlicher,
worin der Widerspruch besteht: Die Annahme `n ≠ 10` ist genau die Negation von `n = 10`.
Man muss `≠` immer als `¬(· = ·)` lesen.
"
-/
Conclusion "Conclusion Logo L09: `n ≠ 10` is negation of `n = 10`. `≠` has to be read as `¬(· = ·)`"

DisabledTactic tauto
