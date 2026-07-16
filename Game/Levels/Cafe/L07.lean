import Game.Metadata

World "Cafe"
Level 7

Title ""

open Set Filter Topology

Statement : Ioo (- 1 / 5) (1 / 5) ∈ 𝓝 (0 : ℝ) := by
  Hint "[Hint mdsff] Rewrite the goal using the theorem `IsOpen.mem_nhds_iff`. "
  rw [IsOpen.mem_nhds_iff]
  · Hint "[Hint tdsg] Try `grind`. "
    grind
  · apply isOpen_Ioo

/---/
TheoremDoc IsOpen.mem_nhds_iff as "IsOpen.mem_nhds_iff" in "Topology"

/---/
TheoremDoc isOpen_Ioo as "isOpen_Ioo" in "Topology"

/---/
DefinitionDoc Set.Ioo as "Set.Ioo" in "Set"

/-- `𝓝 a` is the *neighborhood* of `a`: it consists of all open sets containing `a`. -/
DefinitionDoc nhds as "𝓝"

NewTheorem IsOpen.mem_nhds_iff isOpen_Ioo

NewDefinition Set.Ioo nhds
