import Game.Metadata

World "Cartan"
Level 7

open Topology Filter Set

Introduction "Intro Cartan L07: another example for `filter_upwards`"

/---/
TheoremDoc IsOpen.eventually_mem as "IsOpen.eventually_mem"

Statement {f g : ℝ → ℝ} {a b c : ℝ} (hb : b ∈ Ioo a c)
    (h : ∀ x ∈ Ioo a c, f x = g x) : f =ᶠ[𝓝 b] g := by
  Hint (strict := true) "[Hint evmb1] First establish `∀ᶠ x in 𝓝 b, x ∈ Ioo a c` with `have`."
  have hmem : ∀ᶠ x in 𝓝 b, x ∈ Ioo a c := by
    Hint (hidden := true) "[Hint evem2] An open set containing `a` holds eventually near a:
    apply `IsOpen.eventually_mem`."
    apply IsOpen.eventually_mem _ hb
    apply isOpen_Ioo
  Hint (hidden := true) "[Hint 4j4cl] Try `filter_upwards [{hmem}]`."
  filter_upwards [hmem]
  assumption

NewTheorem IsOpen.eventually_mem
