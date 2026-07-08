import Game.Metadata
import Mathlib.LinearAlgebra.AffineSpace.Slope

World "Slope"
Level 4

open Topology Filter

/-- `Tendsto f (𝓝 a) (𝓝 b)` says that `f x` approaches `b` as `x` approaches `a` —
in usual notation, $\lim_{x \to a} f(x) = b$.

You can read `𝓝 a` as "the points near `a`", so the whole statement reads:
`f` sends points near `a` to points near `b`.

A useful variant: `Tendsto f (𝓝[≠] a) (𝓝 b)` only looks at points near `a`
with `x ≠ a`, so the value `f a` itself plays no role — this is the usual
notion of a limit from calculus.

Similarly, `𝓝[>] a` and `𝓝[<] a` only look at points near `a` with `x > a`
(resp. `x < a`), so they describe one-sided limits: the limit from the right
(resp. from the left).

To type the symbol `𝓝`, write `\nhds`. For the variants, just append the
bracket part: `\nhds[>]`, `\nhds[<]`, and `\nhds[\ne]` for `𝓝[≠]`.
-/
DefinitionDoc Filter.Tendsto as "Tendsto" in "Function"

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
NewDefinition Filter.Tendsto
