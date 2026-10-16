import Game.Metadata

World "Espresso"
Level 4

Title ""

Introduction "Intro Espresso L04"

Statement (a b c : ℤ) :
    a + b + c = 3 →
    a ^ 2 + b ^ 2 + c ^ 2 = 5 →
    a ^ 3 + b ^ 3 + c ^ 3 = 7 →
    a ^ 4 + b ^ 4 = 9 - c ^ 4 := by
  Hint "[Hint grindRing] This goal is a polynomial identity in the integers.
    Not so easy without `grind`."
  Branch
    intro h1 h2 h3
    exfalso
    have hc : c = 3 - a - b := by grind
    rw [hc] at h2 h3
    clear h1
    grind
  grind

Conclusion "Conclusion Espresso L04:
  From the quadratic hypothesis, you see that each of `a`, `b` and `c` is an integer between $-2$ and $2$.
  If you plug in these possible values into the other two hypotheses, you will find that at least one
  of them is always false. So the exact conclusion here is not relevant."
