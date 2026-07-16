import Game.Metadata

World "Cartan"
Level 2

open Filter Topology Set

/-- `IsOpen s` says that `s` is an open set. -/
DefinitionDoc IsOpen as "IsOpen"

/-- `Set.Ioo a b` is the open interval `(a, b)`. -/
DefinitionDoc Set.Ioo as "Set.Ioo"

/---/
TheoremDoc isOpen_Ioo as "isOpen_Ioo"

/---/
TheoremDoc IsOpen.mem_nhds_iff as "IsOpen.mem_nhds_iff"

/- Explain here, the -/
Statement : Ioo (- 1 / 5) (1 / 5) ∈ 𝓝 (0 : ℝ) := by
  rw [IsOpen.mem_nhds_iff]
  · grind
  · apply isOpen_Ioo

NewTheorem IsOpen.mem_nhds_iff isOpen_Ioo
NewDefinition IsOpen Set.Ioo
