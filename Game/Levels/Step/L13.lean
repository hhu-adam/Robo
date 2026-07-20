import Game.Metadata


World "Step"
Level 13

open Finset

Introduction "For every real number `a` we define the *step function*

```
step a := fun x ↦ if x ≤ a then 0 else 1
```

which is `0` up to the point `a` and jumps to `1` after it.

**Boss level:** show that the family of *all* step functions `step a`, `a : ℝ`,
is linearly independent in the function space `ℝ → ℝ` — an uncountable
linearly independent family!"

/-- `step a` is the step function that jumps at the point `a`: it takes the
value `0` for `x ≤ a` and `1` for `x > a`. -/
noncomputable
def step (a : ℝ) : ℝ → ℝ := fun x ↦ if x ≤ a then 0 else 1

/-- `step a : ℝ → ℝ` is the step function with its jump at the point `a`:

```
step a := fun x ↦ if x ≤ a then 0 else 1
```

It takes the value `0` for `x ≤ a` and the value `1` for `x > a`.
Unfold it in a proof with `simp [step]` or `unfold step`. -/
DefinitionDoc step as "step" in "LinearAlgebra"

/-- The family of all step functions `step a`, `a : ℝ`, is linearly independent
in the function space `ℝ → ℝ`. -/
Statement : LinearIndependent ℝ step := by
  Hint "**Math Hint.** Suppose

  ```
  c₁ • step a₁ + c₂ • step a₂ + ⋯ + cₙ • step aₙ = 0    (a₁ < a₂ < ⋯ < aₙ)
  ```

  as functions (using `linearIndependent_iff'`). Pick a point `x` between `a₁` and `a₂`. At this `x` the first
  step function has already jumped, the others have not:
  `step a₁ x = 1` but `step a₂ x = ⋯ = step aₙ x = 0`.
  So evaluating the sum at `x` gives exactly `c₁ = 0`.

  Now the first term is gone and the same argument kills `c₂`, then `c₃`, …
  — every coefficient is `0`, which is linear independence.

  *Repeatedly removing the smallest point* is precisely
  `Finset.induction_on_min` (from an earlier level); the point `x` can be
  chosen using `Finset.min'` of the remaining indices."
  Hint "[Hint iIdiff] Start with `rw [linearIndependent_iff']`, then induct on
    the index set using `Finset.induction_on_min`."
  rw [linearIndependent_iff']
  intro s g
  -- induction on the finite support, peeling off the *smallest* index each time
  induction s using Finset.induction_on_min with
  | empty =>
    simp
  | insert a s ha ih =>
    have has : a ∉ s := by grind
    intro hg i hi
    -- pick a sample point `x` with `a < x ≤ b` for all `b ∈ s`
    obtain hexist : ∃ x, a < x ∧ ∀ b ∈ s, x ≤ b := by
      obtain rfl | hs := s.eq_empty_or_nonempty
      · use a + 1
        simp
      · use (a + s.min' hs) / 2
        have hmin : a < s.min' hs := by
          apply ha
          apply min'_mem
        have h_le : ∀ b ∈ s, s.min' hs ≤ b := by
          apply min'_le
        grind
    obtain ⟨x, hax, hxs⟩ := hexist
    -- evaluate the vanishing linear combination at `x`: only `g a` survives
    have hga : g a = 0 := by
      have hx := congrFun hg x
      -- simp at hx
      have h_sum : (∑ i ∈ s, g i • step i) x = 0 := by
        rw [Finset.sum_apply]
        apply sum_eq_zero
        intro t ht
        simp [step]
        grind
      rw [Finset.sum_insert has, Pi.add_apply, h_sum] at hx
      simp [step] at hx
      grind
    -- drop the `a`-term and apply the induction hypothesis
    have hgs : ∑ i ∈ s, g i • step i = 0 := by
      rw [Finset.sum_insert has, hga, zero_smul, zero_add] at hg
      assumption
    simp at hi
    obtain rfl | hi' := hi
    · assumption
    · apply ih
      apply hgs
      assumption

NewDefinition step

TheoremTab "LinearAlgebra"
