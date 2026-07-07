import Game.Metadata

World "Step"
Level 8

/---/
TheoremDoc Finset.induction_on_min as "Finset.induction_on_min" in "Set"

Statement {s : Finset ℝ} {hs : s.Nonempty} : ∃ a ∈ s, ∀ b ∈ s, a ≤ b := by
  Hint "[Hint indmin] `Finset.induction_on_min` is induction on a finite set:
  prove the statement for `∅`, then show it survives inserting an element `a`
  that is **smaller than everything** already present (`ha`). Template:

  ```
  induction s using Finset.induction_on_min with
  | empty => sorry
  | insert a s ha ih => sorry
  ```

  In the `insert` case, `a` is the witness you need."
  induction s using Finset.induction_on_min with
  | empty =>  contradiction
  | insert a s ha ih =>
    use a
    grind

NewTheorem Finset.induction_on_min

TheoremTab "Set"
