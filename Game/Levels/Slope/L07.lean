import Game.Metadata

World "Slope"
Level 7

open Topology Filter

/---/
TheoremDoc Filter.Tendsto.mono_left as "Tendsto.mono_left" in "Function"

Statement :
    Tendsto (fun (x : ℝ) => |x|) (𝓝[≠] 0) (𝓝 0) := by
  Hint "[Hint monolft] You already proved this limit along `𝓝 0`. State that
    with `have h : Tendsto (fun (x : ℝ) => |x|) (𝓝 0) (𝓝 0)`; then
    `Tendsto.mono_left` says a limit along `𝓝 0` is also a limit along the
    smaller `𝓝[≠] 0`."
  have h : Tendsto (fun (x : ℝ) => |x|) (𝓝 0) (𝓝 0) := by
    apply Continuous.tendsto'
    fun_prop
    grind
  apply h.mono_left
  apply nhdsWithin_le_nhds

NewTheorem Filter.Tendsto.mono_left
