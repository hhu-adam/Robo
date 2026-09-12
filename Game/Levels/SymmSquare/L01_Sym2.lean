import Game.Metadata

World "Symmetric Square"
Level 1

Introduction "Intro Symm L01"

open Sym2

/-- -/
TheoremDoc Sym2.Rel.trans as "Sym2.Rel.trans" in "Relations"

Statement Sym2.Rel.trans {A : Type*} {x y z : A × A} :
    let r := Sym2.Rel A
    r x y → r y z → r x z := by
  Hint "[Hint sy1rel] An unordered pair should not care about order: `\{1,2}` and `\{2,1}` are
    meant to be the same thing. `Sym2.Rel A` makes that precise as a relation on `A × A`,
    built from two rules only: `refl`, saying `(x,y) ∼ (x,y)`, and `swap`, saying
    `(x,y) ∼ (y,x)`."
  intro h₁ h₂
  Hint "[Hint sy1cs1] `Sym2.Rel` is an inductive relation, so `{h₁}` can only come from one
    of those two rules. `cases` splits into exactly these possibilities."
  cases h₁
  · Hint (hidden := true) "[Hint sy1cs2] Now do the same with `{h₂}`."
    cases h₂
    · rfl
    · Hint (hidden := true) "[Hint sy1swp] The two pairs differ by a swap — that is the rule
        `Sym2.Rel.swap`."
      apply Sym2.Rel.swap
  · cases h₂
    · apply Sym2.Rel.swap
    · rfl

/---/
TheoremDoc Sym2.Rel.swap as "Sym2.Rel.swap" in "Quotient"

NewTheorem Sym2.Rel.swap

NewDefinition Sym2.Rel

NewTactic cases

TheoremTab "Quotient"
