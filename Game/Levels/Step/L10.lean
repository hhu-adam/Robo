import Game.Metadata


World "Step"
Level 10

Introduction "So far, linear (in)dependence was only about **finitely many**
vectors. Now: linear independence of an **infinite** family.

For every `a : ℝ`, define the *bump* function
`bump a := fun x ↦ if x = a then 1 else 0`.

**Mini-boss:** show the family `bump a`, `a : ℝ`, is linearly independent."

/-- `bump a` is `1` at `a` and `0` everywhere else. -/
noncomputable
def bump (a : ℝ) : ℝ → ℝ := fun x ↦ if x = a then 1 else 0

/-- `bump a : ℝ → ℝ` takes the value `1` at `x = a` and `0` everywhere else:

```
bump a := fun x ↦ if x = a then 1 else 0
```
-/
DefinitionDoc bump as "bump" in "LinearAlgebra"

/-- The family of all bump functions `bump a`, `a : ℝ`, is linearly independent
in the function space `ℝ → ℝ`. -/
Statement : LinearIndependent ℝ bump := by
  Hint "[Hint bmpiff] Remember the theorem `linearIndependent_iff'`."
  rw [linearIndependent_iff']
  intro s g hg a ha
  Hint "[Hint bmpcong] `hg` is an equality of *functions*. Remember how we
    turned such an equality into a statement about values in an earlier level."
  Hint (hidden := true) "[Hint bmpsimp] Evaluate `hg` at the point `a` using
    `congrFun`, then let `simp [bump, Finset.sum_apply]` collapse the sum."
  have hx := congrFun hg a
  simp [bump, Finset.sum_apply, ha] at hx
  grind

NewDefinition bump

TheoremTab "LinearAlgebra"
