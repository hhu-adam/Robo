import Game.Levels.Shade.L08_ValRightOfSSup

World "Shade"
Level 9

Title ""

Introduction
"[Intro]
 If a continuous function `f` takes a strictly smaller value at the left endpoint `a` than at the
 right endpoint `c` of an interval, then somewhere strictly between the endpoints the function still
 exceeds its value at the left endpoint.
"

open Set FullGrind

/-- If `f`, `f : ℝ → ℝ` is continuous and `a`, `c` (`a c : ℝ`) are points with `a < c` and
`f a < f c`, then there is some `b ∈ Ioo a c` with `f b > f c`. -/
TheoremDoc exists_mem_Ioo_val_gt_left as "exists_mem_Ioo_val_gt_left" in "Shade"

Statement exists_mem_Ioo_val_gt_left {f : ℝ → ℝ} {a c : ℝ} (hf : Continuous f) (hac : a < c)
    (h_lt : f a < f c) : ∃ b ∈ Ioo a c, f b > f a := by
  Hint "[Hint ivIoo] One version of intermediate value theorem is `intermediate_value_Ioo`,
    which says
    ```
    Set.Ioo (f a) (f c) ⊆ f '' Set.Ioo a c
    ```
    Suggestion:  state this inclusion with `have`, use theorem to prove it,
    then see what you can do with it."
  have h : Set.Ioo (f a) (f c) ⊆ f '' Set.Ioo a c := by
    apply intermediate_value_Ioo
    · grind
    Hint "The remaining goal is the continuity statement `Continuous f`. Use `fun_prop`,
      which automatically proves such function properties."
    · fun_prop
  Hint (strict := true) "[Hint Ioontps] Can now apply our version of intermediate value theorem
    to an arbitrary value between `f c` and `f a`, i.e. to an arbitrary value in `Ioo (f c) (f a)`.
    Suggestion: state and prove `(Ioo (f c) (f a)).Nonempty`."
  have h_ne : (Ioo (f a) (f c)).Nonempty := by
    use (f a + f c) / 2
    grind
  obtain ⟨fval, hfval⟩ := h_ne
  obtain hfval' := h hfval
  choose b hb using hfval'
  use b
  grind

/---/
TheoremDoc intermediate_value_Ioo as "intermediate_value_Ioo" in "Topology"
NewTheorem intermediate_value_Ioo
