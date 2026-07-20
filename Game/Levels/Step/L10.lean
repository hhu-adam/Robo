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
  Hint "[Hint bmpiff] Start with `rw [linearIndependent_iff']`, then `intro`
    the finite index set `s`, the coefficients `g`, the hypothesis that the
    combination vanishes, and an index `a ∈ s`."
  rw [linearIndependent_iff']
  intro s g hg a ha
  Hint "[Hint bmpcong] Evaluate the vanishing combination `hg` at the point
    `a` with `congrFun`."
  Hint (hidden := true) "[Hint bmpsimp] `simp [bump, Finset.sum_apply]`
    collapses the sum: every term `g i • bump i a` is `0` unless `i = a`,
    since `a ∈ s` this leaves exactly `g a`."
  have hx := congrFun hg a
  simp [bump, Finset.sum_apply, ha] at hx
  grind

NewDefinition bump

TheoremTab "LinearAlgebra"
