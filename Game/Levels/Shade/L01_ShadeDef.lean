import Game.Levels.Culmen.L07_CsSup_mem_closure

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

/- COMMENT
I'm trying to mimick the definitions & API of "odd" and "even" in Mathlib.

*Comment resolved(Wenrong):* I think we should use the other direction, which is
  `a ∉ Sun f ↔ a ∈ Shade f`. It's the right direction of simplification.
-/

/-- `Shade f` is the set of shade points of `f`: those `s` for which there exists some
`t > s` with `f t > f s`. -/
DefinitionDoc Shade as "Shade" in "Shade"

/-- `Sun f` is the set of sunny points of `f`: those `s` with with `f t ≤ f s` for all `t > s`. -/
DefinitionDoc Sun as "Sun" in "Shade"

/-- A point lies in the shade exactly when it is not a sunny point. -/
TheoremDoc mem_Shade_iff_not_mem_Sun as "mem_Shade_iff_not_mem_Sun" in "Shade"

Statement mem_Shade_iff_not_mem_Sun (f : ℝ → ℝ) (a : ℝ) : a ∉ Sun f ↔ a ∈ Shade f := by
  Hint "Both sides are set-builder memberships. Unfold them with `simp [Shade, Sun]` and let
  `simp` push the negation through the `∀`."
  simp [Shade, Sun]

attribute [game_simp] mem_Shade_iff_not_mem_Sun

Conclusion "Conclusion Shade L01: saved as `mem_Shade_iff_not_mem_Sun`."

NewDefinition Shade Sun

TheoremTab "Shade"
