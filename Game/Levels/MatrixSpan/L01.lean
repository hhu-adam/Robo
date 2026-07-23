import Game.Metadata

World "Span"
Level 1

Title "Scaling Vectors"

Introduction "Welcome to *Span*.

The mathematical stage for this world is a **module** (over `ℝ`, a *vector space*).  You don't
need any theory: a module `V` is simply a collection of **vectors** that you can

* **add** together (`x + y`), and
* **scale** by a real number (`a • x`, where `a : ℝ`).

The symbol `•` is written `\\smul`.  Scaling interacts with addition exactly the way you would hope.
As a first taste: scaling a vector by `2` is the same as adding it to itself.  That fact is called
`two_smul`.
"

open Real Function Set Finset

/-- `two_smul` : scaling a vector by `2` gives `x + x`, i.e. `(2 : ℝ) • x = x + x`. -/
TheoremDoc two_smul as "two_smul" in "LinearAlgebra"

Statement {V : Type*} [AddCommMonoid V] [Module ℝ V] (x : V) :
    (2 : ℝ) • x = x + x := by
  Hint "This is exactly what `two_smul` says. Rewrite with it using `rw [two_smul]`."
  rw [two_smul]

NewTheorem two_smul

TheoremTab "LinearAlgebra"
