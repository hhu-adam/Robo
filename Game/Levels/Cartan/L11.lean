import Game.Metadata
import Mathlib.Topology.LocallyConstant.Basic

World "Cartan"
Level 11

open Topology Filter

Introduction "
A function `f` is *locally constant* if every point has a neighborhood on which
`f` is constant. In Mathlib this is captured by `IsLocallyConstant f`, which is
defined as: the preimage `f ⁻¹' s` of *every* set `s` is open.

Here you show that a locally constant function is *eventually* equal to its
value at `x`, for the neighborhood filter `𝓝 x`.
"

/-- `IsLocallyConstant f` says that every point has a neighborhood on which `f` is
constant; it is defined as: the preimage of every set under `f` is open. -/
DefinitionDoc IsLocallyConstant as "IsLocallyConstant"

/---/
TheoremDoc IsLocallyConstant.eventually_eq as "IsLocallyConstant.eventually_eq"

Statement IsLocallyConstant.eventually_eq {f : ℝ → ℝ} {x : ℝ}
    (hf : IsLocallyConstant f) : ∀ᶠ y in 𝓝 x, f y = f x := by
  have h : IsOpen (f ⁻¹' {f x}) := by
    apply hf
  filter_upwards [IsOpen.eventually_mem h rfl]
  intro y hy
  assumption

NewDefinition IsLocallyConstant
