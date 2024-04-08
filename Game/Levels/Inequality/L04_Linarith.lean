import Game.Metadata

World "Inequality"
Level 4

Title "Linarith"

Introduction
"
**Robo**: Dann versuchs mal hiermit!

$$
\\begin{aligned}
  5 * y &\\le 35 - 2 * x \\\\
  2 * y &\\le x + 3
\\end{aligned}
$$
"

Statement (x y : ℤ) (h₂ : 5 * y ≤ 35 - 2 * x) (h₃ : 2 * y ≤ x + 3) : y ≤ 5 := by
  linarith

Conclusion "**Du**: Boah, nicht schlecht."
