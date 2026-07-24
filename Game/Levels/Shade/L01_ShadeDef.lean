import Game.Levels.Aquarium.L07_CsSup_mem_closure

World "Shade"
Level 1

Title ""

Introduction "Intro Shade L01: the two kinds of points.

Think of the graph of `f` lit by a sun shining from the right.  A point `s` lies in the *shade*
if some later point rises above it, and it is *sunny* if nothing to its right ever gets higher:

```
Shade f := {s : ℝ | ∃ t > s, f t > f s}
Sun   f := {s : ℝ | ∀ t > s, f t ≤ f s}
```

These two conditions are negations of each other, and your first job is to prove exactly that.
"

open Set FullGrind

def Shade (f : ℝ → ℝ) := {s : ℝ | ∃ t > s, f t > f s}
def Sun (f : ℝ → ℝ) : Set ℝ := {s : ℝ | ∀ t > s, f t ≤ f s}
/- TODO
Should this be reformulated? "≤ and < are highly favored over ≥ and > in mathlib"
-/

/-- `Shade f` is the set of shade points of `f`: those `s` for which there exists some
`t > s` with `f t > f s`.
```
Shade f := {s : ℝ | ∃ t > s, f t > f s}
```
-/
DefinitionDoc Shade as "Shade" in "Shade"

/-- `Sun f` is the set of sunny points of `f`: those `s` with with `f t ≤ f s` for all `t > s`.
```
Sun f := {s : ℝ | ∀ t > s, f t ≤ f s}
```
-/
DefinitionDoc Sun as "Sun" in "Shade"

/-- Not being in the sun means lying in the shade. -/
TheoremDoc not_mem_Sun_iff_mem_Shade as "not_mem_Sun_iff_mem_Shade" in "Shade"

/- We're trying to mimick the Mathlib API for Odd and Even here, which includes the following two
simp lemmas:
`not_odd_iff_even`
`not_even_iff_odd`
-/

Statement not_mem_Sun_iff_mem_Shade (f : ℝ → ℝ) (a : ℝ) : a ∉ Sun f ↔ a ∈ Shade f := by
  Hint "Both sides are set-builder memberships. Unfold them with `simp [Shade, Sun]` and let
  `simp` push the negation through the `∀`."
  simp [Shade, Sun]

attribute [game_simp] not_mem_Sun_iff_mem_Shade

Conclusion "Conclusion Shade L01: saved as `not_mem_Sun_iff_mem_Shade`."

NewDefinition Shade Sun

TheoremTab "Shade"
