import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs

open Finset

noncomputable
def step (a : ℝ) : ℝ → ℝ := fun x ↦ if x ≤ a then 0 else 1

/-- The family of all step functions `step a`, `a : ℝ`, is linearly independent
in the function space `ℝ → ℝ`. -/
theorem linearIndependent_step : LinearIndependent ℝ step := by
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
      rcases s.eq_empty_or_nonempty with rfl | hs
      · use a + 1
        simp
      ·
        -- use (a + s.min' hs) / 2
        have hmin := ha _ (s.min'_mem hs)
        have h_le : ∀ b ∈ s, s.min' hs ≤ b := s.min'_le
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
    rcases Finset.mem_insert.mp hi with rfl | hi'
    · assumption
    · apply ih
      apply hgs
      assumption

/-- Hence for any `S : Set ℝ`, the subfamily `{step a | a ∈ S}` is linearly
independent — no extra hypothesis on `S` is needed. -/
theorem linearIndependent_step_restrict (S : Set ℝ) :
    LinearIndependent ℝ (fun a : S ↦ step a) :=
  linearIndependent_step.comp _ Subtype.val_injective
