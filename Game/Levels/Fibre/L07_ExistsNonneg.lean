import Game.Levels.Fibre.L06_ExistsNonpos

World "Fibre"
Level 7

Introduction "Intro Fibre L07"

open Set FullGrind

/- The lemma below already in the latest mathlib. After bumping mathlib,
we could delete this lemma. -/
/-- `fun_prop` only knows `Continuous.neg` in the pointwise form `fun x ↦ -(f x)`.
When the goal is stated with the `Pi` negation `-f`, it sees `Neg.neg f x` and gives up,
so we register the same statement in that shape. -/
@[fun_prop]
lemma Continuous.neg' {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Neg Y] [ContinuousNeg Y] {f : X → Y} (hf : Continuous f) :
    Continuous (fun x ↦ (-f) x) := hf.neg

/-- Somewhere strictly between the two zeros of `f`, the function is non-negative. -/
TheoremDoc exists_mem_Ioo_val_nonneg as "exists_mem_Ioo_val_nonneg" in "Fibre"

Statement exists_mem_Ioo_val_nonneg {f : ℝ → ℝ} (hf1 : Continuous f)
    (hf2 : ∀ y, (f ⁻¹' {y}).ncard = 2) {x₁ x₂ : ℝ} (hx_lt : x₁ < x₂)
    (hx : f ⁻¹' {0} = {x₁, x₂}) : ∃ x ∈ Ioo x₁ x₂, 0 ≤ f x := by
  have hf2' : ∀ y, ((-f) ⁻¹' {y}).ncard = 2 := by
    intro y
    have h : (-f) ⁻¹' {y} = f ⁻¹' {-y} := by
      ext x
      simp
      grind
    rw [h]
    apply hf2
  have hx' : (-f) ⁻¹' {0} = {x₁, x₂} := by
    have h : (-f) ⁻¹' {0} = f ⁻¹' {0} := by
      ext x
      simp
    rw [h]
    apply hx
  have h_neg : ∃ x ∈ Ioo x₁ x₂, (-f) x ≤ 0 := by
    apply exists_mem_Ioo_val_nonpos _ hf2' hx_lt hx'
    fun_prop
  obtain ⟨x, hx_mem, hx_le⟩ := h_neg
  use x
  constructor
  · assumption
  simp at hx_le
  grind

TheoremTab "Fibre"
