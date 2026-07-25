import Game.Metadata

World "Cartan"
Level 7

open Topology Filter Set

/---/
TheoremDoc IsOpen.eventually_mem as "IsOpen.eventually_mem"

Statement {f g : ℝ → ℝ} {a b c : ℝ} (ha : a ∈ Ioo b c)
    (h : ∀ x ∈ Ioo b c, f x = g x) : f =ᶠ[𝓝 a] g := by
  Hint (strict := true) "[Hint evmb1] First establish `∀ᶠ x in 𝓝 a, x ∈ Ioo b c` with `have`."
  have hmem : ∀ᶠ x in 𝓝 a, x ∈ Ioo b c := by
    Hint (hidden := true) "[Hint evem2] An open set containing `a` holds eventually near a:
    apply `IsOpen.eventually_mem`."
    apply IsOpen.eventually_mem _ ha
    apply isOpen_Ioo
  Hint "[Hint 4j4cl] Try `filter_upwards [{hmem}]`."
  filter_upwards [hmem]
  assumption

NewTheorem IsOpen.eventually_mem
