import Game.Metadata
import Mathlib.Topology.LocallyConstant.Basic

World "Cartan"
Level 8

open Filter Topology

/---/
TheoremDoc Filter.Eventually.exists as "Filter.Eventually.exists"

/---/
TheoremDoc inv_lt_zero as "inv_lt_zero"

Statement : ¬ ( ∀ᶠ x in 𝓝[≠] (0 : ℝ), (fun (x : ℝ) ↦ 1/x) x > 5) := by
  intro h
  have h' : ∀ᶠ x in 𝓝[<] (0 : ℝ), (fun (x : ℝ) ↦ 1/x) x > 5 := by
    apply h.filter_mono
    apply nhdsWithin_mono
    grind
  have : ∀ᶠ (x : ℝ) in 𝓝[<] 0, (fun (x : ℝ) ↦ 1 / x) x > 5 ∧ x ∈ Set.Iio 0 := by
    apply eventually_and.mpr
    constructor
    · assumption
    · apply eventually_mem_nhdsWithin
  have exist_aux : ∃ (x : ℝ), (fun (x : ℝ) ↦ 1 / x) x > 5 ∧ x ∈ Set.Iio 0 := by
    apply this.exists
  obtain ⟨x, hx5, hxneg⟩ := exist_aux
  simp at hxneg
  obtain h := inv_lt_zero.mpr hxneg
  grind

NewTheorem Filter.Eventually.exists inv_lt_zero
