import Game.Metadata

World "Hamel"
Level 10

Introduction "Intro Hamel L10"

/-- `bump a` is `1` at `a` and `0` everywhere else. -/
noncomputable
def bump (a : ℝ) : ℝ → ℝ := fun x ↦ if x = a then 1 else 0

/-- `bump a : ℝ → ℝ` takes the value `1` at `x = a` and `0` everywhere else:

```
bump a := fun x ↦ if x = a then 1 else 0
```
-/
DefinitionDoc bump as "Function.bump" in "Function"

/-- The family of all bump functions `bump a`, `a : ℝ`, is linearly independent
in the function space `ℝ → ℝ`. -/
Statement : LinearIndependent ℝ bump := by
  Hint "[Hint bmpinf] So far, linear independence concerned *finitely many* vectors; this
    family is indexed by all of `ℝ`. Writing `b_a` for `bump a`,
    $$
    b_a(x) = \\begin\{cases}
      1 & \\text\{if } x = a, \\\\ %(new line)
      0 & \\text\{otherwise,}
    \\end\{cases}
    $$
    and such an infinite family is linearly independent exactly when each of its *finite*
    subfamilies is."
  Hint (hidden := true) "[Hint bmpiff] Remember the theorem `linearIndependent_iff'`."
  rw [linearIndependent_iff']
  intro s g hg a ha
  Hint "[Hint bmpcong] `hg` is an equality of *functions*. Remember how we
    turned such an equality into a statement about values in an earlier level."
  Hint (hidden := true) "[Hint bmpsimp] Evaluate `hg` at the point `a` using
    `congrFun`, then let `simp [bump, Finset.sum_apply]` collapse the sum."
  have hx := congrFun hg a
  simp [bump, ha] at hx
  grind

NewDefinition bump

TheoremTab "LinearAlgebra"
