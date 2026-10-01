import Game.Metadata
import Mathlib.Analysis.Calculus.Deriv.Slope

World "Slope"
Level 11

open Topology Filter

Statement {x : ℝ} {f₁ f₂ g f' : ℝ → ℝ} (h₀ : ∀ x, f₁ x = f₂ x)
    (h1 : HasDerivAt (fun y ↦ f₁ y * g y) (f' x) x) :
    HasDerivAt (fun y ↦ f₂ y * g y) (f' x) x := by
  Hint "[Hint cv7qa] The hypothesis `{h1}` is almost the goal, i.e. the two functions only differ
    in `{f₁}` versus `{f₂}`, and they are the same pointwise by `h₀`."
  convert h1
  Hint (hidden := true) "[Hint cv2mk] What remains is an equation of functions. Compare
    them pointwise with `funext`, then use h₀."
  funext x₁
  rw [h₀]

NewTactic convert
