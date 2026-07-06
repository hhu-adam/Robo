import Game.Levels.Shade.L07_InterValue

World "Shade"
Level 8

Title ""

open Set

def Shade (f : ℝ → ℝ) : Set ℝ := {s : ℝ | ∃ t > s, f t > f s}

def Sun (f : ℝ → ℝ) : Set ℝ := (Shade f)ᶜ

/-- `Shade f` is the set of shadow points of `f`: those `s` for which there exists some
`t > s` with `f t > f s`. -/
DefinitionDoc Shade as "Shade" in "Shade"

/-- If `a` is not a shadow point, then `f x ≤ f a` for every `x > a`. -/
TheoremDoc mem_sun as "mem_sun" in "Shade"

Statement mem_sun {f : ℝ → ℝ} {a : ℝ} (h : a ∈ Sun f) (x : ℝ) (h_lt : a < x) :
    f x ≤ f a := by
  Hint "[Hint shadeBC]Argue by contradiction."
  by_contra hc
  push Not at hc
  /- how to cite a variable here. -/
  Hint "[Hint notshade] Note that there is a element that is greater than `a` with function
    value greater than `f a`, which contradicts to the assumption that `a ∈ Sun f`. "
  have : a ∈ Shade f := by
    use x
  contradiction

Conclusion "Conclusion LightAndShade L01: saved as `not_mem_shade`."

NewDefinition Shade

TheoremTab "Shade"
