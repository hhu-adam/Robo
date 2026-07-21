import Game.Levels.Culmen.L07_CsSup_mem_closure

World "Shade"
Level 1

Title ""

open Set FullGrind

def Shade (f : ℝ → ℝ) := {s : ℝ | ∃ t > s, f t > f s}
def Sun (f : ℝ → ℝ) : Set ℝ := {s : ℝ | ∀ t > s, f t ≤ f s}

@[game_simp]
lemma mem_Shade_iff_not_mem_Sun (f : ℝ → ℝ) (a : ℝ): a ∈ Shade f ↔ a ∉ Sun f := by
  simp_log [Shade, Sun]
/- COMMENT
I'm trying to mimick the definitions & API of "odd" and "even" in Mathlib.
-/


/-- `Shade f` is the set of shade points of `f`: those `s` for which there exists some
`t > s` with `f t > f s`. -/
DefinitionDoc Shade as "Shade" in "Shade"

/-- `Sun f` is the set of sunny points of `f`: those `s` with with `f t ≤ f s` for all `t > s`. -/
DefinitionDoc Sun as "Sun" in "Shade"

/-- If `a` is a sunny point, then `f x ≤ f a` for every `x > a`. -/
TheoremDoc mem_sun as "mem_sun" in "Shade"

Statement mem_sun {f : ℝ → ℝ} {a : ℝ} (h : a ∈ Sun f) (x : ℝ) (h_lt : a < x) :
    f x ≤ f a := by
  Hint (hidden := true) "[Hint w4joj] Try `simp [Sun]`."
  simp_log [Sun] at h
  grind

Conclusion "Conclusion LightAndShade L01: saved as `mem_sun`."

NewDefinition Shade Sun

TheoremTab "Shade"
