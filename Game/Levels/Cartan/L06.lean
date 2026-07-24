import Game.Metadata

World "Cartan"
Level 6

open Topology Filter

/-- `filter_upwards [h₁, …, hₙ]` proves a goal of the form `∀ᶠ x in f, p x`
from hypotheses `hᵢ : ∀ᶠ x in f, pᵢ x`: it reduces the goal to showing that
`p x` follows pointwise from the `pᵢ x`. -/
TacticDoc filter_upwards

Statement {f g : ℝ → ℝ} {a : ℝ} (ha : a < 0) (h : ∀ x < 0, f x = g x) :
    f =ᶠ[𝓝 a] g := by
  have : ∀ᶠ x in 𝓝 a, x < 0 := by
    apply eventually_lt_nhds ha
  filter_upwards [this]
  assumption

NewTactic filter_upwards
NewHiddenTactic «in»
NewDefinition Filter.EventuallyEq
