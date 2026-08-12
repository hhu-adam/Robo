import Game.Metadata

World "Symmetric Square"
Level 3

Introduction "Intro Symm L03"

open Sym2

attribute [local instance] Sym2.Rel.setoid

/- (1, -2) and (-2, 1) are equal as unordered pairs of integers. -/

Statement : (⟦ (1, -2) ⟧ : Sym2 ℤ) = ⟦ (-2, 1) ⟧ := by
  Hint "[Hint sy3quo] The quotient `Quotient s` collects the elements of `A` up to `≈`, and
    `⟦a⟧` (typed `\\[[` and `\\]]`) is the class of `a`. So `Sym2 ℤ` consists of *unordered*
    pairs of integers, and the goal asks you to forget the order."
  Hint (hidden := true) "[Hint sy3snd] Congruent elements have the same class — that is
    `Quotient.sound`, and it reduces the goal to a statement about the two pairs."
  Branch
    simp [Quotient.eq]
    apply Sym2.Rel.swap
  apply Quotient.sound
  Hint (hidden := true) "[Hint sy3swp] The two pairs differ by a swap, which is the rule
    `Sym2.Rel.swap`."
  apply Sym2.Rel.swap

/-- -/
TheoremDoc Quotient.sound as "Qutient.sound" in "Qutient"

/-- -/
TheoremDoc Quotient.eq as "Qutient.eq" in "Qutient"

NewTheorem Quotient.sound Quotient.eq
NewDefinition Sym2

TheoremTab "Quotient"
