import Game.Metadata

World "Cartan"
Level 8

open Filter Topology

Introduction "Intro Cartan L08: introduce the function $x ↦ \\tfrac{1}{x}$"

/---/
TheoremDoc Filter.eventually_iff as "eventually_iff" in "Filter"

/---/
TheoremDoc inv_lt_inv₀ as "inv_lt_comm₀"  in "≤"
/---/
TheoremDoc lt_inv_comm₀ as "lt_inv_comm₀" in "≤"
/---/
TheoremDoc inv_lt_inv₀ as "inv_lt_inv₀" in "≤"


Statement :  ∀ᶠ (x : ℝ) in atTop, 1 / x < 1 / 5 := by
  Hint "[Hint zntfk] For a filter `𝓕`, `∀ᶠ x in 𝓕, p x` says that `p x` holds *eventually*,
  i.e. the set `\{ x | p x}` is a member of 𝓕. You can do it by `rw`ing with
  `eventually_iff`."
  rw [eventually_iff]
  Hint "Second filter axiom says filter is upward closed (`mem_of_superset`)."  -- A
  Hint (hidden := true) "[Hint fmt6] Note that `\{x | 6 ≤ x}` is a subset of left hand side."
  apply mem_of_superset (mem_atTop 6)
  intro x hx
  simp at hx ⊢
  Hint "[Hint ilinv] Note that `inv_lt_inv₀` is useful here."
  rw [inv_lt_inv₀]
  · grind
  · grind
  · grind

NewTheorem Filter.eventually_iff inv_lt_inv₀ lt_inv_comm₀ inv_lt_inv₀
