import Game.Metadata


World "Function"
Level 7

Title "congr_arg"


Introduction
"
**Robo**: Manchmal will man ein Goal der Form `f x = f y` lösen, indem man zeigt, dass
`x = y` ist. In dem Fall kann man `apply congr_arg` brauchen.
"

open Function

Statement {x y : ℤ} (f : ℤ → ℤ) (h : x = y) :
    let g : ℤ → ℤ := fun x ↦ x + 3;
    f (g 0) = f 3 := by
  apply congr_arg
  rfl

/---/
TheoremDoc congr_arg as "congr_arg" in "Function"

OnlyTactic apply rfl
NewTheorem congr_arg -- tactic `congr` would have same effect
TheoremTab "Function"

Conclusion ""
