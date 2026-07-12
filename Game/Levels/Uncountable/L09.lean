import Game.Metadata
import Mathlib.SetTheory.Cardinal.Arithmetic

World "Uncountable"
Level 9

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
  rw [← Cardinal.power_def]
  rw [h_card]
  rw [Cardinal.mk_fintype]
  rw [power_natCast]
  apply Cardinal.power_nat_le
  rfl

/---/
TheoremDoc Cardinal.mk_fintype as "Cardinal.mk_fintype" in "Cardinal"

/---/
TheoremDoc Cardinal.power_natCast as "Cardinal.power_natCast" in "Cardinal"

/---/
TheoremDoc Cardinal.power_nat_le as "Cardinal.power_nat_le" in "Cardinal"

NewTheorem Cardinal.mk_fintype Cardinal.power_natCast Cardinal.power_nat_le
