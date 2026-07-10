import Game.Metadata

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
TheoremDoc tendsto_const_nhds as "tendsto_const_nhds" in "Function"

Statement (a c : ℝ) :
    Tendsto (fun (x : ℝ) => c) (𝓝 a) (𝓝 c) := by
  Hint "[Hint tcnst] The constant function sends every point to `c` — in
    particular, points near `a` go to points near `c`. This is the theorem
    `tendsto_const_nhds`; apply it."
  apply tendsto_const_nhds

NewTheorem tendsto_const_nhds
NewDefinition Filter.Tendsto
