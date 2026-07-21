import Game.Metadata


World "Step"
Level 10

open Finset

/- This level introduces `Finset.min'_le`. -/

/---/
TheoremDoc Finset.min'_le as "Finset.min'_le" in "Set"

Statement (s : Finset ℝ) (hs : s.Nonempty) (x : ℝ) (hx : x ∈ s) : s.min' hs ≤ x := by
  apply Finset.min'_le s x hx

NewTheorem Finset.min'_le

TheoremTab "Set"
