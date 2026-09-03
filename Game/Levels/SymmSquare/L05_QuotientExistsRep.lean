import Game.Metadata

World "Symmetric Square"
Level 5

Introduction "Intro Symm L05"

open Sym2

attribute [local instance] Sym2.Rel.setoid

Statement {A : Type*} (q : Sym2 A) : ∃ a b : A, (⟦ (a, b) ⟧ : Sym2 A) = q := by
  Hint "[Hint sy5rep] Every element of a quotient comes from the original type: `Quotient.exists_rep`
    produces a representative. An element of `Sym2 A` is a class of *pairs*, so a representative
    of `{q}` is a pair `(a, b) : A × A` — that is what lets you argue about an arbitrary
    unordered pair by picking one ordered pair standing for it."
  obtain h := Quotient.exists_rep q
  obtain ⟨⟨a, b⟩, hab⟩ := h
  Hint (hidden := true) "[Hint sy5use] Now `{a}` and `{b}` are the two elements you are
    looking for."
  use a, b


/---/
TheoremDoc Quotient.exists_rep as "Quotient.exists_rep" in "Quotient"

NewTheorem Quotient.exists_rep

TheoremTab "Quotient"
