import Game.Metadata


World "Terrace"
Level 3

open Finset

Introduction "Intro Terrace L03"

/- This level introduces `Finset.min'_le`. -/

/---/
TheoremDoc Finset.min'_le as "Finset.min'_le" in "Set"

Statement (s : Finset ℝ) (hs : s.Nonempty) (x : ℝ) (hx : x ∈ s) : s.min' hs ≤ x := by
  Hint "[Hint minle] In the previous level you used one half of what makes `Finset.min' s hs`
    the smallest element of `s`: it lies in s. Here is the other half: it is below every
    element of s, so in particular below `x`."
  Hint (hidden := true) "[Hint minleh] This is `Finset.min'_le`. It needs to know that x is
    an element of s, so hand it the hypothesis `hx`."
  apply Finset.min'_le s x hx

NewTheorem Finset.min'_le

TheoremTab "Set"
