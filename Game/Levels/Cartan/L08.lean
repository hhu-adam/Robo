import Game.Metadata

World "Cartan"
Level 8

open Topology Filter Set

/---/
TheoremDoc IsOpen.eventually_mem as "IsOpen.eventually_mem"

Statement {f g : ℝ → ℝ} {a b c : ℝ} (ha : a ∈ Ioo b c)
    (h : ∀ x ∈ Ioo b c, f x = g x) : f =ᶠ[𝓝 a] g := by
  have : ∀ᶠ x in 𝓝 a, x ∈ Ioo b c := by
    apply IsOpen.eventually_mem _ ha
    apply isOpen_Ioo
  filter_upwards [this]
  assumption

NewTheorem IsOpen.eventually_mem
