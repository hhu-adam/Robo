import Game.Metadata

World "Luna"
Level 7

Title ""

Introduction
"
**Lina**:  Genug von `omega`, jetzt bin ich wieder an der Reihe.
"

Statement (x y : ℚ) (h₁ : 35/11 * y ≤ 35/2 - 22/21 * x) (h₂ : 8/9 * y ≤ x + 17/8) : y ≤ 34/7 := by
  Hint "**Du**:  Das muss ich mir erst noch einmal untereinander schreiben.  Gegeben ist:

  $$
  \\begin\{aligned}
    \\tfrac\{35}\{11}\\cdot y &\\le -\\tfrac\{22}\{21}\\cdot x + \\tfrac\{35}\{2}  \\\\
    \\tfrac\{8}\{9} \\cdot y &\\le x + \\tfrac\{17}\{8}
  \\end\{aligned}
  $$

  Und wir sollen zeigen:
  $$
  y ≤ \\tfrac\{34}\{7}
  $$

  Robo??

  Lina grinst.
  "
  linarith

Conclusion "**Du**: Nicht schlecht!"
