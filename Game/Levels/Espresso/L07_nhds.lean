import Game.Metadata

World "Espresso"
Level 7

Title ""

Introduction "Intro Espresso L07"

open Set Filter Topology FullGrind

Statement : Ioo (- 1 / 5) (1 / 5) ∈ 𝓝 (0 : ℝ) := by
  Hint "[Hint mdsff]
    `Ioo (-1 / 5) (1 / 5)` is the open interval between $\\tfrac\{-1}\{5}$ and $\\tfrac\{1}\{5}$,
    i.e. $(\\tfrac\{-1}\{5},\\tfrac\{1}\{5})$.
    `𝓝 0` is the filter of neighborhoods of `0` (sets containing `0` in their interior).
    Joke about filter/coffee/`grind`.
    As the interval is open, can proceed with new theorem `IsOpen.mem_nhds_iff`. "
  rw [IsOpen.mem_nhds_iff]
  Hint "[Hint 33o0v] See: Now just need to prove that `0` lies in the interval
    $(\\tfrac\{-1}\{5},\\tfrac\{1}\{5})$,
    and that the interval is indeed open."
  · Hint (hidden := true) "[Hint tdsg] Try `grind`"
    grind
  · Hint "[Hint hdioioo] Open interval is an open set. New theorem: `isOpen_Ioo`."
    apply isOpen_Ioo

/---/
TheoremDoc IsOpen.mem_nhds_iff as "IsOpen.mem_nhds_iff" in "Topology"

/---/
TheoremDoc isOpen_Ioo as "isOpen_Ioo" in "Topology"

NewTheorem IsOpen.mem_nhds_iff isOpen_Ioo

NewDefinition Set.Ioo nhds
