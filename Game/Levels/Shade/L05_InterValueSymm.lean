import Game.Levels.Shade.L04_InterValue

World "Shade"
Level 5

Title ""

Introduction
"[Intro]
 The mirror image of the previous level.  If a continuous function `f` takes a strictly smaller
 value at the left endpoint `a` than at the right endpoint `b` of an interval, then somewhere
 strictly between the endpoints the function already exceeds its value at that left endpoint.
"

open Set FullGrind

/-- If `f` is continuous on `[a, b]` with `a < b` and `f a < f b`, then there is some
`s ∈ Ioo a b` with `f s > f a`. -/
TheoremDoc exists_mem_Ioo_gt' as "exists_mem_Ioo_gt'" in "Shade"

Statement exists_mem_Ioo_gt' {f : ℝ → ℝ} {a b : ℝ} (hf : Continuous f) (hab : a < b)
    (h_lt : f a < f b) : ∃ s ∈ Ioo a b, f s > f a := by
  have h : Set.Ioo (f a) (f b) ⊆ f '' Set.Ioo a b := by
    apply intermediate_value_Ioo
    · grind
    · fun_prop
  have hs : (Ioo (f a) (f b)).Nonempty := by
    use (f a + f b) / 2
    grind
  obtain ⟨z, hz⟩ := hs
  obtain h1 := h hz
  choose x hx using h1
  use x
  grind

/-- -/
TheoremDoc intermediate_value_Ioo as "intermediate_value_Ioo" in "Topology"
NewTheorem intermediate_value_Ioo
