import Game.Metadata

World "Slope"
Level 6

open Topology Filter Metric FullGrind Set


Introduction "[Intro] Remember from Cafe:
  `𝓝[≠] a` – points near `x` near `a` with `x ≠ a`
  `𝓝[>] a` – points near `x` near `a` with `x > a`
More formally, for any subset `s : ℝ`, the elements of `𝓝[s] a` are the intersections of `s` with
neighbourhoods of `a`.
So:
   `𝓝[≠] a` – shortcut for `𝓝[\\{0}ᶜ] a`
   `𝓝 a`    – same as `𝓝[univ] a`
"

/- TODO
  Introduced notation for set complements on Piazza!
  (We intially had it in there, but I think it has gone lost. Here we need it.)
  *Resolved*
-/

Statement : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0 := by
  Hint "[Hint nwln] Remember `nhdsWithin_mono` from Cafe.  To apply it here, first establish
    `𝓝 (0 : ℝ) = 𝓝[univ] 0` with `have`, then `rw` using this equality."
  have : 𝓝 (0 : ℝ) = 𝓝[univ] 0:= by
    simp
  rw [this]
  apply nhdsWithin_mono
  grind

Conclusion ""
