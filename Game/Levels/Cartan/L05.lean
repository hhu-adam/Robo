import Game.Metadata

World "Cartan"
Level 5

open Filter Topology Set

/-- `𝓝[>] a` is the filter of right neighborhoods of `a`, i.e. the neighborhoods
of `a` inside `Set.Ioi a`. It is defined as `𝓝 a ⊓ 𝓟 (Set.Ioi a)`. -/
DefinitionDoc nhdsWithin as "𝓝[>]"

/-- `Set.Iio b` is the unbounded open interval `(-∞, b)`. -/
DefinitionDoc Set.Iio as "Set.Iio"

/-- `Set.Ioi a` consists of all elements greater than `a`, i.e. the unbounded
open interval `(a, ∞)`. -/
DefinitionDoc Set.Ioi as "Set.Ioi"

/---/
TheoremDoc Filter.mem_inf_iff_superset as "Filter.mem_inf_iff_superset"

/---/
TheoremDoc isOpen_Iio as "isOpen_Iio"

/---/
TheoremDoc Set.mem_Iio as "Set.mem_Iio"

/---/
TheoremDoc Set.mem_Ioi as "Set.mem_Ioi"

Statement : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := by
  rw [mem_nhdsWithin]
  use Ioo (-1) 1
  constructor
  · apply isOpen_Ioo
  grind

NewTheorem Filter.mem_inf_iff_superset isOpen_Iio Set.mem_Iio Set.mem_Ioi
NewDefinition nhdsWithin Set.Iio Set.Ioi
