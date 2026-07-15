import Game.Metadata

World "Cartan"
Level 2

open Filter Topology

/-- `IsOpen s` says that `s` is an open set. -/
DefinitionDoc IsOpen as "IsOpen"

/---/
TheoremDoc mem_of_mem_nhds as "mem_of_mem_nhds"

/---/
TheoremDoc IsOpen.mem_nhds as "IsOpen.mem_nhds"

/---/
TheoremDoc IsOpen.mem_nhds_iff as "IsOpen.mem_nhds_iff"

/- Explain here, the -/
Statement IsOpen.mem_nhds_iff {a : ℝ} {s : Set ℝ} (hs : IsOpen s) :
    s ∈ 𝓝 a ↔ a ∈ s := by
  constructor
  · intro h
    apply mem_of_mem_nhds
    assumption
  · intro h
    apply IsOpen.mem_nhds
    · assumption
    · assumption

NewTheorem mem_of_mem_nhds IsOpen.mem_nhds
NewDefinition IsOpen
