import Game.Metadata

World "Cartan"
Level 2

open Filter Topology

Introduction "
Not every generalized point sits next to an actual point. The filter
`atTop` on `ℝ` is the generalized point 'at infinity': a set belongs to
`atTop` when it contains every sufficiently large number, i.e. when it is a
'neighborhood of `+∞`'.

In this level you prove that the *open* ray beyond `b` is also a
neighborhood of `+∞`.
"

/-- `atTop` is the filter of all sets that contain every sufficiently large
element — all `x ≥ b`, for some bound `b`. Think of it as the generalized
point 'at infinity'. -/
DefinitionDoc Filter.atTop as "atTop"

/---/
TheoremDoc Filter.mem_atTop as "Filter.mem_atTop"

/- The open ray beyond `b` is a neighborhood of `+∞`. -/
Statement {b : ℝ} : {x : ℝ | b < x} ∈ atTop := by
  Hint "[Hint pkzt] By `Filter.mem_atTop`, the ray `\{x | b + 1 ≤ x}` belongs to
  `atTop`, and your set contains it. So the second filter axiom applies."
  obtain h := (Filter.mem_atTop (b + 1))
  apply Filter.mem_of_superset h
  grind

NewTheorem Filter.mem_atTop
NewDefinition Filter.atTop
