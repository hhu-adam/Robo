import Game.Metadata

World "Slope"
Level 4

open Topology Filter

Introduction "`Tendsto f (𝓝 a) (𝓝 b)` says that `f x` approaches `b` as `x` approaches `a` —
in usual notation, $\\lim_{x \\to a} f(x) = b$.

You already met the neighborhoods `𝓝 a` and `𝓝[s] a` on the planet *Cafe*.
Since `𝓝 a` consists of the points near `a`, the whole statement reads:
`f` sends points near `a` to points near `b`."

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
