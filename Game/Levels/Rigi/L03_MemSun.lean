import Game.Levels.Rigi.L02_ShadeDefSymm

World "Rigi"
Level 3

Title ""

open Set

Introduction "Intro Rigi L03"

/-- If `a` is a sunny point, then `f a ≥ f x` for every `x` with `x > a`. -/
TheoremDoc mem_sun as "mem_sun" in "Shade"

Statement mem_sun (preamble := grind_mode 1) {f : ℝ → ℝ} {a : ℝ} (h : a ∈ Sun f) (x : ℝ) (h_lt : x > a) :
    f a ≥ f x := by
  Hint (hidden := true) "[Hint w4joj] Try `simp [Sun]`."
  simp [Sun] at h
  grind


Conclusion "Conclusion Rigi L03: saved as `mem_sun`."

TheoremTab "Shade"
