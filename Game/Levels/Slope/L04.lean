import Game.Metadata

World "Slope"
Level 4

open Topology Filter

Introduction "`Tendsto f (𝓝 a) (𝓝 b)` says that `f x` approaches `b` as `x` approaches `a` —
in usual notation, $\\lim_{x \\to a} f(x) = b$.

You already met the neighborhoods `𝓝 a` and `𝓝[s] a` on the planet *Cafe*.
Since `𝓝 a` consists of the points near `a`, the whole statement reads:
`f` sends points near `a` to points near `b`."

/-- `Tendsto f (𝓝 a) (𝓝 b)` says that `f x` approaches `b` as `x` approaches `a` —
in usual notation, $\lim_{x \to a} f(x) = b$.

Combining `Tendsto` with the restricted neighborhoods gives the limit notions
from calculus:

* `Tendsto f (𝓝[≠] a) (𝓝 b)` only looks at points near `a` with `x ≠ a`,
  so the value `f a` itself plays no role — this is the usual limit.
* `Tendsto f (𝓝[>] a) (𝓝 b)` and `Tendsto f (𝓝[<] a) (𝓝 b)` describe the
  one-sided limits from the right and from the left.

To type the symbol `𝓝`, write `\nhds`.
-/
DefinitionDoc Filter.Tendsto as "Tendsto" in "Function"

/---/
TheoremDoc tendsto_const_nhds as "tendsto_const_nhds" in "Function"

Statement (a c : ℝ) :
    Tendsto (fun (x : ℝ) => c) (𝓝 a) (𝓝 c) := by
  Hint "[Hint tcnst] The constant function sends every point to `c` — in
    particular, points near `a` go to points near `c`. This is the theorem
    `tendsto_const_nhds`; apply it."
  apply tendsto_const_nhds

NewTheorem tendsto_const_nhds
NewDefinition Filter.Tendsto
