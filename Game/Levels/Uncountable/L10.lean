import Game.Metadata
import Mathlib.SetTheory.Cardinal.Arithmetic

World "Uncountable"
Level 10

Introduction "Intro Uncountable L10"

universe u

noncomputable section

open Module

namespace Cardinal

/---/
TheoremDoc Cardinal.cardinal_eq_of_finite_basis as "Cardinal.cardinal_eq_of_finite_basis" in "Cardinal"

Statement cardinal_eq_of_finite_basis {K V ι : Type u} [Field K] [AddCommGroup V]
    [Module K V] [Fintype ι] (h_card : #K = ℵ₀) (h_basis : Basis ι K V) : #V ≤ ℵ₀ := by
  Hint "[Hint cardBasis] The strategy is to show `#V = #K ^ #ι` first: a basis identifies
    `V` with the function space `ι → K`."
  Hint (hidden := true) "[Hint cardBasisEquiv] Have a look at `{h_basis}.equivFun.toEquiv`
    and remember `Cardinal.mk_congr` from a previous level."
  rw [Cardinal.mk_congr h_basis.equivFun.toEquiv]
  Hint (hidden := true) "[Hint pdfr] The cardinality of a function type is a power.
    Remember the theorem `Cardinal.power_def`."
  rw [← Cardinal.power_def]
  Hint (hidden := true) "[Hint hcrw] You know what `#K` is: rewrite with `{h_card}`."
  rw [h_card]
  Hint (hidden := true) "[Hint finm] Try `simp`."
  simp
  Hint "[Hint pwnl] Raising an infinite cardinal to a finite power does
    not make it bigger."
  Hint (hidden := true) "[Hint pwnlsh] Try to apply `Cardinal.power_nat_le`."
  apply Cardinal.power_nat_le
  rfl

/---/
TheoremDoc Cardinal.power_nat_le as "Cardinal.power_nat_le" in "Cardinal"

NewTheorem Cardinal.power_nat_le
