import Game.Levels.Shade.L09_InterValue

World "Shade"
Level 10

Title ""

Introduction
"[Intro]
 The mirror image of the previous level.  If a continuous function `f` takes a strictly larger
 value at the left endpoint `a` than at the right endpoint `c` of an interval, then somewhere
 strictly between the endpoints the function already exceeds its value at the right endpoint.
"

open Set FullGrind

/-- If `f`, `f : ℝ → ℝ` is continuous and `a`, `c` (`a c : ℝ`) are points with `a < c` and
`f a > f c`, then there is some `b ∈ Ioo a c` with `f b > f c`. -/
TheoremDoc exists_mem_Ioo_val_gt_right as "exists_mem_Ioo_val_gt_right" in "Shade"

Statement exists_mem_Ioo_val_gt_right {f : ℝ → ℝ} {a c : ℝ} (hf : Continuous f) (hac : a < c)
    (h_lt : f c < f a) : ∃ b ∈ Ioo a c, f b > f c := by
  have h : Set.Ioo (f c) (f a) ⊆ f '' Set.Ioo a c := by
    Hint (hidden := true) "[Hint itvIoo] Just `apply` `intermediate_value_Ioo'`."
    apply intermediate_value_Ioo'
    · grind
    · fun_prop
  have h_ne : (Ioo (f c) (f a)).Nonempty := by
    use (f c + f a) / 2
    grind
  obtain ⟨fval, hfval⟩ := h_ne
  obtain hfval' := h hfval
  choose b hb using hfval'
  use b
  grind

/---/
TheoremDoc intermediate_value_Ioo' as "intermediate_value_Ioo'" in "Topology"
NewTheorem intermediate_value_Ioo'
