import Game.Metadata

World "Terrace"
Level 1

Introduction "On `Hamel` every linearly independent family was either finite or,
like the bump functions, indexed so that a single evaluation point already
isolated one coefficient. The step functions are harder: no point separates one
of them from all the others at once. Instead one peels the coefficients off
**one at a time, starting from the smallest jump**.

This planet builds the little bit of `Finset` machinery that makes that peeling
precise — induction on the smallest element, and the smallest element `Finset.min'`
itself — and then uses it on the boss."

open FullGrind

/---/
TheoremDoc Finset.induction_on_min as "Finset.induction_on_min" in "Set"

Statement {s : Finset ℝ} {hs : s.Nonempty} : ∃ a ∈ s, ∀ b ∈ s, a ≤ b := by
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
