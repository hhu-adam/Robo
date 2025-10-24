import Game.Metadata
import Game.Levels.Cantor.L02_CantorPowerset

World "Cantor"
Level 3

Title ""

/-
Introduction
"
**Du**: Jetzt habe ich aber noch nicht erkannt, was daran „diagonal“ ist.

**Cantor**: Nein?  Na dann pass auf!  Wir machen das jetzt noch einmal  l a n g s a m.

Er wühlt wieder in seinem Zylinder.  Ein Kompass.  Eine Violine. Eine Dose Schnupftabak.

**Cantor**:  Ach nein, wir machen das anders.

Er greift noch einmal tief in seinen Zylinder hinein,
und holt einen ganzen Stapel Papier heraus. Den wirft er euch zu.
Ihr seht euch die Zettel nacheinander an.
"
-/
Introduction "`INTRO` Intro Cantor L03"

/-
Conclusion "
  **Cantor**:  Gut gemacht!

  Er hat angefangen mit ein paar Kakteen zu jonglieren,
  aber offenbar verfolgt er dennoch irgendwie, was ihr macht.
"
-/
Conclusion "Conclusion Cantor L03"

open Function Set

Statement : ∀ (x : ℝ), IsFixedPt (fun (x : ℝ) ↦ |x|) x ↔ 0 ≤ x := by
-- The function here is simply called `abs` in mathlib,
-- but let's not introduced too much additional notation
-- when it's only needed once.
  /-
  Hint "**Robo**: Also `|x|` ist einfach der übliche Betrag der reellen Zahl `x`.
  Und was `IsFixedPt` bedeutet findest du vermutlich mit `unfold` heraus."
  -/
  Hint "Try `unfold IsFixedPt`"
  unfold IsFixedPt
  /-
  Hint "**Du**:  Ähm …

  **Robo**:  `IsFixedPt` soll vermutlich “is fixed point” heißen.
  Jedenfalls bedeutet `IsFixedPt f x` offenbar gerade `f x = x`.
  "
  -/
  Hint "Story"
  intro x
  constructor
  /-
  Hint "**Robo**:  So weit, so gut."
  -/
  Hint "Story"
  · intro h
    rw [← h]
    --Branch
    --  positivity
    clear h
    /- Hint "**Robo**: `simp` kann man immer mal probieren." -/
    Hint "Try `simp`"
    simp -- only [abs_nonneg]
  · intro h
    -- rw [abs_of_nonneg h]
    /- Hint (hidden := true) "**Robo**: `simp` kann man immer mal probieren." -/
    Hint "Try `simp`"
    simp
    assumption

NewDefinition Function.IsFixedPt absValue
-- absFunction
