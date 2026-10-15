import Game.Metadata

World "Espresso"
Level 7

Title ""

Introduction "Espresso L07"

open Set Filter Topology FullGrind

Statement : Ioo (- 1 / 5) (1 / 5) ∈ 𝓝 (0 : ℝ) := by
  Hint "[Hint mdsff]
    `𝓝 a` is the filter of neighborhoods of `a` (sets containing `a` in their interior).
    Joke about filter/coffee/grind.
    `Ioo x y` is the open interval between `x` and `y`, i.e. $(x,y)$.
    As the interval is open, can proceed with new theorem `IsOpen.mem_nhds_iff`. "
  rw [IsOpen.mem_nhds_iff]
  · Hint (hidden := true) "[Hint tdsg] Try `grind`"
    grind
  · Hint "[Hint hdioioo] Open interval is a open set. New theorem: `isOpen_Ioo`."
    apply isOpen_Ioo

/---/
TheoremDoc IsOpen.mem_nhds_iff as "IsOpen.mem_nhds_iff" in "Topology"

/---/
TheoremDoc isOpen_Ioo as "isOpen_Ioo" in "Topology"

NewTheorem IsOpen.mem_nhds_iff isOpen_Ioo

NewDefinition Set.Ioo nhds
