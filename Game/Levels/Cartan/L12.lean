import Game.Metadata
import Mathlib.Topology.LocallyConstant.Basic

World "Cartan"
Level 12

-- #check IsLocallyConstant

open Topology Filter

/-- `IsLocallyConstant f` says that every point has a neighborhood on which `f` is constant. -/
DefinitionDoc IsLocallyConstant as "IsLocallyConstant"

/---/
TheoremDoc IsLocallyConstant.eventually_eq as "IsLocallyConstant.eventually_eq"

Statement {f g : ℝ → ℝ} {x : ℝ} (hf : IsLocallyConstant f) (hg : IsLocallyConstant g)
    (h : f x = g x) : ∀ᶠ y in 𝓝 x, f y = g y := by
  have : ∀ᶠ y in 𝓝 x, f y = f x := by
    apply IsLocallyConstant.eventually_eq hf x
  rw [h] at this
  filter_upwards [this, IsLocallyConstant.eventually_eq hg x]
  intro y h1 h2
  rw [h1, h2]

NewTheorem IsLocallyConstant.eventually_eq
NewDefinition IsLocallyConstant
