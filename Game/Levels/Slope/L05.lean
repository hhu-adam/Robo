import Game.Metadata
import Mathlib.LinearAlgebra.AffineSpace.Slope

World "Slope"
Level 5

open Topology Filter

/---/
TheoremDoc Continuous.tendsto' as "Continuous.tendsto'" in "Function"

Statement :
    Tendsto (fun (x : ℝ) => |x|) (𝓝 0) (𝓝 0) := by
  Hint "[Hint ctdst] The absolute value function is continuous, so its limit
    at `0` is simply its value there: `|0| = 0`. In Lean, apply the theorem
    `Continuous.tendsto'`."
  apply Continuous.tendsto'
  Hint (hidden := true) "[Hint rmbfp] Remember we have `fun_prop`"
  fun_prop
  grind

NewTheorem Continuous.tendsto'
