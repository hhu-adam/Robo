import Game.Metadata
import Mathlib.Topology.LocallyConstant.Basic

World "Cartan"
Level 10

open Filter Topology

/---/
TheoremDoc nhdsWithin_mono as "nhdsWithin_mono"

/---/
TheoremDoc Filter.Eventually.and as "Filter.Eventually.and"

/---/
TheoremDoc Filter.Eventually.exists as "Filter.Eventually.exists"

/---/
TheoremDoc inv_lt_zero as "inv_lt_zero"

Statement : ¬ ( ∀ᶠ x in 𝓝[≠] (0 : ℝ), (fun (x : ℝ) ↦ 1/x) x > 5) := by
  intro h
  have h' : ∀ᶠ x in 𝓝[<] (0 : ℝ), (fun (x : ℝ) ↦ 1/x) x > 5 := by
    apply h.filter_mono
    apply nhdsWithin_mono
    intro x hx
    simp [Set.mem_Iio] at hx ⊢
    grind
  obtain ⟨x, hx5, hxneg⟩ := (h'.and eventually_mem_nhdsWithin).exists
  simp [Set.mem_Iio] at hxneg
  obtain h := inv_lt_zero.mpr hxneg
  grind

NewTheorem nhdsWithin_mono Filter.Eventually.and Filter.Eventually.exists inv_lt_zero
