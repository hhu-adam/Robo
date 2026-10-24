import Game.Levels.Shade.L02_ShadeDefSymm

World "Shade"
Level 3

Title ""

open Set
Introduction "Intro Shade L03"


/-- If `a` is a sunny point, then `f x ≤ f a` for every `x > a`. -/
TheoremDoc mem_sun as "mem_sun" in "Shade"

Statement mem_sun (preamble := grind_mode 1) {f : ℝ → ℝ} {a : ℝ} (h : a ∈ Sun f) (x : ℝ) (h_lt : a < x) :
    f x ≤ f a := by
  Hint (hidden := true) "[Hint w4joj] Try `simp [Sun]`."
  simp [Sun] at h
  grind

Conclusion "Conclusion Shade L03: saved as `mem_sun`."

TheoremTab "Shade"
