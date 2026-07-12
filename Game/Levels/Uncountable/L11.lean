import Game.Metadata
import Game.Levels.Uncountable.L09
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Data.Rat.Denumerable
import Mathlib.Analysis.Real.Cardinality

World "Uncountable"
Level 11

universe u

noncomputable section

open Module

namespace Cardinal

/- Boss level: `ℝ` is not a finite-dimensional `ℚ`-vector space. -/

Statement : ¬ FiniteDimensional ℚ ℝ := by
  Hint "[Hint boss] Suppose `ℝ` were finite-dimensional over `ℚ`. Then
    `Basis.ofVectorSpace ℚ ℝ` is a finite basis, so `#ℝ ≤ ℵ₀` by
    `cardinal_eq_of_finite_basis`. This contradicts `Cardinal.not_countable_real`."
  Branch
    -- TODO: Eduart Bopp's proof
    Hint "[Hint bossAlt] `let B := Basis.ofVectorSpace ℚ ℝ` gives you a basis of `ℝ`
      over `ℚ`. Then argue by contradiction, using `Cardinal.not_countable_real`
      and the lemma `cardinal_eq_of_finite_basis` from the previous levels.
      You might want to start by showing `#ℚ = ℵ₀`."
    let B := Basis.ofVectorSpace ℚ ℝ
    by_contra
    letI : Countable ℚ := by
      infer_instance
    have h_ℚ : #ℚ = Cardinal.aleph0 := Cardinal.mk_eq_aleph0 ℚ
    have : ¬ Countable ℝ := by
      apply Uncountable.not_countable
    have cardinal_ineq : #ℝ ≤ Cardinal.aleph0 :=
      cardinal_eq_of_finite_basis h_ℚ B
    have h3 := Cardinal.not_countable_real
    rw [← Cardinal.le_aleph0_iff_set_countable] at h3
    simp only [Cardinal.mk_univ] at h3
    contradiction
  by_contra h
  apply Cardinal.not_countable_real
  rw [← Cardinal.le_aleph0_iff_set_countable]
  rw [Cardinal.mk_univ]
  let B := Basis.ofVectorSpace ℚ ℝ
  apply cardinal_eq_of_finite_basis _ B
  apply Cardinal.mk_eq_aleph0 ℚ

/---/
TheoremDoc Cardinal.not_countable_real as "Cardinal.not_countable_real" in "Cardinal"

NewTheorem Cardinal.not_countable_real
