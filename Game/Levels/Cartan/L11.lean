import Game.Metadata
import Mathlib.Topology.LocallyConstant.Basic

World "Cartan"
Level 11

open Filter Topology

/---/
TheoremDoc Filter.eventually_iff as "Filter.eventually_iff"

/---/
TheoremDoc inv_lt_inv₀ as "inv_lt_inv₀"

Statement :  ∀ᶠ x in atTop, (fun (x : ℝ) ↦ 1/x) x < 1 / 5 := by
  rw [eventually_iff]
  apply Filter.mem_of_superset (Filter.mem_atTop 6)
  intro x hx
  simp at hx ⊢
  rw [inv_lt_inv₀]
  · grind
  · grind
  · grind

NewTheorem Filter.eventually_iff inv_lt_inv₀
