import Game.Metadata

World "Cartan"
Level 8

open Filter Topology

/-- `𝓝[>] a` is the filter of right neighborhoods of `a`, i.e. the neighborhoods
of `a` inside `Set.Ioi a`. It is defined as `𝓝 a ⊓ 𝓟 (Set.Ioi a)`. -/
DefinitionDoc nhdsWithin as "𝓝[>]"

/-- `Set.Ioo a b` is the open interval `(a, b)`. -/
DefinitionDoc Set.Ioo as "Set.Ioo"

/-- `Set.Iio b` is the unbounded open interval `(-∞, b)`. -/
DefinitionDoc Set.Iio as "Set.Iio"

/-- `Set.Ioi a` consists of all elements greater than `a`, i.e. the unbounded
open interval `(a, ∞)`. -/
DefinitionDoc Set.Ioi as "Set.Ioi"

/---/
TheoremDoc isOpen_Iio as "isOpen_Iio"

/---/
TheoremDoc Set.mem_Iio as "Set.mem_Iio"

Statement : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := by
  rw [nhdsWithin]
  rw [mem_inf_iff_superset]
  use Set.Iio 1
  constructor
  · rw [IsOpen.mem_nhds_iff isOpen_Iio]
    grind
  · use Set.Ioi 0
    constructor
    · apply mem_principal_self
    · intro x hx
      obtain ⟨h1, h0⟩ := hx
      grind

NewTheorem isOpen_Iio Set.mem_Iio
NewDefinition nhdsWithin Set.Ioo Set.Iio Set.Ioi
