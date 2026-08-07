import Game.Metadata

World "Symmetric Square"
Level 5

Introduction
"Intro Symm L05:

Every element of a quotient comes from an element of the original type: for `q : Quotient s`
there is always a representative `a` with `⟦a⟧ = q`. This is witnessed by `Quotient.exists_rep`:

```
Quotient.exists_rep (q : Quotient s) : ∃ a, ⟦a⟧ = q
```

Note that the representative is not unique: any `a'` with `a ≈ a'` does the job just as well.
Nevertheless, choosing one is what lets you prove a statement about an arbitrary unordered pair
`q : Sym2 A` by proving it for a pair `(a, b) : A × A` representing `q`.

"

open Sym2

attribute [local instance] Sym2.Rel.setoid

Statement {A : Type*} (q : Sym2 A) : ∃ a b : A, (⟦ (a, b) ⟧ : Sym2 A) = q := by
  Hint "An element of `Sym2 A` is a class of *pairs*, so a representative of `{q}` is a
  pair `(a, b) : A × A`. Obtain one with `Quotient.exists_rep`."
  obtain h := Quotient.exists_rep q
  obtain ⟨⟨a, b⟩, hab⟩ := h
  Hint (hidden := true) "Now `{a}` and `{b}` are the two elements you are looking for."
  use a, b


/-- -/
TheoremDoc Quotient.exists_rep as "Quotient.exists_rep" in "Quotient"

NewTheorem Quotient.exists_rep

TheoremTab "Quotient"
