import Game.Metadata

World "Terrace"
Level 1

Introduction "Intro Terrace L01"

open FullGrind

/---/
TheoremDoc Finset.induction_on_min as "Finset.induction_on_min" in "Set"

Statement {s : Finset ℝ} {hs : s.Nonempty} : ∃ a ∈ s, ∀ b ∈ s, a ≤ b := by
  Hint "On `Hamel` we prove that bump functions are linearly independent. In this planet we are
  going to prove *step functions* are linearly independent. First we discuss some
  results and techniques related to finite set."
  Hint "[Hint indmin] `Finset.induction_on_min` is induction on a finite set:
  prove the statement for `∅`, then show it survives inserting an element `a`
  that is **smaller than everything** already present (`ha`). Template:

  ```
  induction s using Finset.induction_on_min with a s ha ih
  · sorry
  · sorry
  ```

  In the `insert` case, `a` is the witness you need."
  Branch
    induction s using Finset.induction_on_min with
    | empty => contradiction
    | insert a s ha ih =>
      use a
      grind
  induction s using Finset.induction_on_min with a s ha ih
  · contradiction
  · use a
    grind


NewTheorem Finset.induction_on_min

TheoremTab "Set"
