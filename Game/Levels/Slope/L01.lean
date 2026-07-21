import Game.Metadata
import Mathlib.LinearAlgebra.AffineSpace.Slope

World "Slope"
Level 1

/---/
DefinitionDoc slope as "slope" in "Function"

Statement {x y : ℝ} {f : ℝ → ℝ} :
    slope f x y = (f y - f x) / (y - x)  := by
  Hint "[Hint sldf] Rewrite with `slope_def_field`."
  rw [slope_def_field]

/---/
TheoremDoc slope_def_field as "slope_def_field" in "Function"

NewTheorem slope_def_field
NewDefinition slope
