import Game.Metadata

World "Espresso"
Level 1

Title ""

Introduction "Intro Espresso L01"

Statement (a c : ℝ) (h : a ≠ c) : a < c ∨ c < a := by
  Hint "[Hint lt] Try to use the theorem `lt_trichotomy` to discuss relations between `a` and `c`
  ```
  have h := lt_trichotomy a c
  ```
  "
  have h := lt_trichotomy a c
  Hint "[Hint 815af] You need to distinguish cases."
  Hint (hidden := true) "[Hint dy3w7] Try `obtain h | h | h := h`"
  obtain h | h | h := h
  · Hint "[Hint tg1] new tactic: `grind`"
    left
    assumption
  · contradiction
  · Hint (hidden := true) "[Hint tg2] try `grind` again"
    right
    assumption
    
/--
Typicall used with `obtain` to distinguish the three cases `x < y`, `x = y` und `x > y` zu unterscheiden:
```
obtain h | h | h := lt_trichotomy x y
```
-/
TheoremDoc lt_trichotomy as "lt_trichotomy" in "≤"
NewTheorem lt_trichotomy

Conclusion "Espresso L01"
