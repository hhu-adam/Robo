import Game.Metadata
import Mathlib.Topology.LocallyConstant.Basic

World "Cartan"
Level 8

open Filter Topology Set

/---/
TheoremDoc Filter.eventually_and as "Filter.eventually_and"

/---/
TheoremDoc eventually_mem_nhdsWithin as "eventually_mem_nhdsWithin"

/---/
TheoremDoc Filter.Eventually.filter_mono as "Filter.Eventually.filter_mono"

/---/
TheoremDoc nhdsWithin_le_nhds as "nhdsWithin_le_nhds"

/---/
TheoremDoc lt_inv_comm₀ as "lt_inv_comm₀"

Statement : ∀ᶠ x in 𝓝[>] (0 : ℝ), (fun (x : ℝ) ↦ 1/x) x > 5 := by
  have h : (0 : ℝ) < 1/5 := by grind
  have hx :  ∀ᶠ (x : ℝ) in 𝓝[>] 0, x ∈ Set.Ioi 0 ∧ x < 1 / 5 := by
    apply eventually_and.mpr
    constructor
    · apply eventually_mem_nhdsWithin
    · suffices : ∀ᶠ (x : ℝ) in 𝓝 0, x < 1 / 5
      · apply this.filter_mono
        apply nhdsWithin_le_nhds
      · apply eventually_lt_nhds h
  filter_upwards [hx]
  intro x ⟨hx1, hx2⟩
  simp at hx1
  simp at hx2 ⊢
  rw [lt_inv_comm₀]
  · assumption
  · grind
  · grind

NewTheorem Filter.eventually_and eventually_mem_nhdsWithin Filter.Eventually.filter_mono
  nhdsWithin_le_nhds lt_inv_comm₀
