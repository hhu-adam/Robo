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
  · left
    assumption
  · contradiction
  · right
    assumption

/--
[Doc.Theorem] `lt_trichotomy`:
Typically used with `obtain` to split a proof concerning `x` and `y` into the three cases
`x < y`, `x = y` and `x > y`:
```
obtain h | h | h := lt_trichotomy x y
```
-/
TheoremDoc lt_trichotomy as "lt_trichotomy" in "≤"
NewTheorem lt_trichotomy

Conclusion "Conclusion Espresso L01"
