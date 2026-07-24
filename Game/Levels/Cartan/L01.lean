import Game.Metadata

World "Cartan"
Level 1

open Filter Topology

Introduction "Intro Cartan L01: Remember that for a point `a` in `ℝ` (`a : ℝ`), `𝓝 a` is the set
of all neighbourhoods of a, i.e. subsets of ℝ that contain an open ball around a."

/---/
TheoremDoc Filter.univ_mem as "Filter.univ_mem"

/---/
TheoremDoc Filter.mem_of_superset as "Filter.mem_of_superset"

/---/
TheoremDoc Filter.inter_mem as "Filter.inter_mem"

/- Third axiom of filter, for the neighborhood filter. -/
Statement {a : ℝ} {s t : Set ℝ} (hs : s ∈ 𝓝 a) (ht : t ∈ 𝓝 a) :
    s ∩ t ∈ 𝓝 a := by
  Hint "[Hint zmbq]
  Need to show that the intersection of two neighborhoods of `a` is
  still a neighborhood of a.

  `𝓝 a` is a filter, so this is an instance of the third filter
  axiom, recorded in Mathlib as `Filter.inter_mem`."
  apply Filter.inter_mem hs ht

Conclusion "Conclusion Cartan L01: Are there any other filters?"

NewTheorem Filter.univ_mem Filter.mem_of_superset Filter.inter_mem
NewDefinition Filter
