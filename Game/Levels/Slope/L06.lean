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
-/

/---/
TheoremDoc nhdsWithin_le_nhds as "nhdsWithin_le_nhds" in "Function"

/- TODO
   Split this into two levels.
   1. as a reminder, prove the statement from `nhdsWithin_mono`, which was included in Cafe;
      see main proof below.
   2. prove with `nhdsWithin_le_nhds` – this is what is used in remainder of planet,
      see Statement2 below.
-/

Statement : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0 := by
  Hint "[Hint nwln] Remember `nhdsWithin_mono` from Cafe.  To apply it here, first establish
    `𝓝 (0 : ℝ) = 𝓝[univ] 0` with `have`, then `rw` using this equality."
  have : 𝓝 (0 : ℝ) = 𝓝[univ] 0:= by
    simp_log
  rw [this]
  apply nhdsWithin_mono
  grind

Conclusion ""

lemma Statement2 : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0  := by
  Hint "[Hint csrcg] Can also prove this directly `nhdsWithin_le_nhds`."
  apply nhdsWithin_le_nhds


NewTheorem nhdsWithin_le_nhds
