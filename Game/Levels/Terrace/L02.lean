import Game.Metadata


World "Terrace"
Level 2

open Finset

Introduction "Intro Terrace L02"

/- In the previous level you showed that a nonempty finite set of reals has a
smallest element. Mathlib packages this smallest element as `Finset.min'`.
This level introduces `Finset.min'_mem`. -/

/---/
TheoremDoc Finset.min'_mem as "Finset.min'_mem" in "Set"

Statement (s : Finset ℝ) (hs : s.Nonempty) : s.min' hs ∈ s := by
  Hint "[Hint minmem] For a nonempty finite set `s`, Mathlib writes its smallest element as
    `Finset.min' s hs`, where the second argument is the proof `hs` that s is nonempty.
    Being the smallest element of s, it is in particular an element of s."
  Hint (hidden := true) "[Hint minmemh] This is `Finset.min'_mem`."
  apply Finset.min'_mem

NewDefinition Finset.min'
NewTheorem Finset.min'_mem

TheoremTab "Set"
