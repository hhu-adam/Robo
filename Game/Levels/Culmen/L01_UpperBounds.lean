import Game.Metadata

World "Culmen"
Level 1

Introduction "Intro Culmen L01: bounded above means having an upper bound.

A number `b` is an *upper bound* of a set `s` when it lies above every element of `s`, written
`b ∈ upperBounds s`.  A set is *bounded above*, `BddAbove s`, exactly when at least one such upper
bound exists.  So the moment someone hands you a concrete upper bound, boundedness follows: in this
level you turn the witness `b` into a proof of `BddAbove s`.
"

open Set FullGrind

Statement {s : Set ℝ} {b : ℝ} (hb : b ∈ upperBounds s) : BddAbove s := by
  Hint "[Hint upbd] `BddAbove s` just says the set of upper bounds is nonempty. You already
  have one upper bound, namely `b` — provide it as the witness with `use`."
  use b

/-- -/
DefinitionDoc upperBounds as "upperBounds" in "Set"

/-- -/
DefinitionDoc BddAbove as "BddAbove" in "Set"

NewDefinition upperBounds BddAbove

Conclusion ""
