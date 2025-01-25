import Game.Metadata


World "Vieta"
Level 8

Title "congr_arg"


Introduction
"Die Kampfgeräusche kommen näher. Vieta gibt euch zwei weitere Blätter."

open Function

Statement {x y : ℤ} (f : ℤ → ℤ) (h : x = y) :
    let g : ℤ → ℤ := fun x ↦ x + 3;
    f (g 0) = f 3 := by
  Hint "**Robo**: Oh, das ist ein Fall für `congr_arg`.  Wenn du schon weiß, dass `x = y, erhälst du
 `f x = f y` mit `apply congr_arg`."
  apply congr_arg
  rfl

/---/
TheoremDoc congr_arg as "congr_arg" in "Function"

OnlyTactic apply rfl
NewTheorem congr_arg -- tactic `congr` would have same effect
TheoremTab "Function"

Conclusion ""
