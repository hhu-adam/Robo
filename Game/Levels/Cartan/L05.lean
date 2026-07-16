import Game.Metadata

World "Cartan"
Level 5

open Filter Topology Set

/-- `𝓝[>] a` is the filter of right neighborhoods of `a`, i.e. the neighborhoods
of `a` inside `Set.Ioi a`. It is defined as `𝓝 a ⊓ 𝓟 (Set.Ioi a)`. -/
DefinitionDoc nhdsWithin as "𝓝[>]"

/-- `Set.Ioi a` consists of all elements greater than `a`, i.e. the unbounded
open interval `(a, ∞)`. -/
DefinitionDoc Set.Ioi as "Set.Ioi"

/---/
TheoremDoc mem_nhdsWithin as "mem_nhdsWithin"

/---/
TheoremDoc Set.mem_Ioi as "Set.mem_Ioi"

Statement : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := by
  rw [mem_nhdsWithin]
  use Ioo (-1) 1
  constructor
  · apply isOpen_Ioo
  grind

NewTheorem mem_nhdsWithin Set.mem_Ioi
NewDefinition nhdsWithin Set.Ioi
