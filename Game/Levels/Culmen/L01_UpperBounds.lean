import Game.Metadata

World "Culmen"
Level 1

Introduction "Intro Culmen L01: bounded above means having an upper bound."

open Set FullGrind

Statement {s : Set ℝ} {b : ℝ} (hb : b ∈ upperBounds s) : BddAbove s := by
  Hint "[Hint upbd] Given a subset `s` of a set `T` (`s : Set T`) and an element `b` of T (`b : T`),
    `b ∈ upperBounds s` means that b is an *upper bound* of s: `s ≤ b` for every element of s.

    For subset `s` of a set `T` (`s : Set T`), `BddAbove s` means that there exists some `b` in T
    (`b : T`) such that `b ∈ upperBounds s`."
  Hint (hidden := true) "[Hint s88tx] You already have one upper bound, namely `b`.
    Provide it as witness with `use`."
  use b

NewDefinition upperBounds BddAbove


Conclusion ""
