import Game.Levels.Rigi.L08_ValRightOfSSup

World "Rigi"
Level 9

Title ""


Introduction
"Intro Rigi L09: Intermediate value theorem: `intermediate_value_Ioo`."


open Set

/-- If `f`, `f : ℝ → ℝ` is continuous and `a`, `c` (`a c : ℝ`) are points with `a < c` and
`f a < f c`, then there is some `b` in $(a, c)$ with `f b > f a`. -/
TheoremDoc exists_mem_Ioo_val_gt_left as "exists_mem_Ioo_val_gt_left" in "Shade"

Statement exists_mem_Ioo_val_gt_left (preamble := grind_mode 1) {f : ℝ → ℝ} {a c : ℝ} (hf : Continuous f) (hac : a < c)
    (h_lt : f a < f c) : ∃ b ∈ Ioo a c, f b > f a := by
  Hint (strict := true)
  "[Hint ivIoo] One version of intermediate value theorem is `intermediate_value_Ioo`,
  which says
  ```
  Set.Ioo (f a) (f c) ⊆ f '' Set.Ioo a c
  ```
  Suggestion:  state this inclusion with `have`, use theorem to prove it,
  then see what you can do with it."
  have h : Set.Ioo (f a) (f c) ⊆ f '' Set.Ioo a c := by
    apply intermediate_value_Ioo
    · grind
    · fun_prop
  Hint (strict := true) (hidden := true)
   "[Hint Ioontps] Apply `{h}` to an arbitrary value in $(f(a),f(c))$.
    Suggestion: state and prove `… ∈ (Ioo (f a) (f c))` for some explicit value."
  Branch
    have h_ne : (Ioo (f a) (f c)).Nonempty := by
      use (f a + f c) / 2
      grind
    obtain ⟨fval, hfval⟩ := h_ne
    obtain hfval' := h hfval
  have hfval' : (f a + f c) / 2 ∈ (Ioo (f a) (f c)) := by
    grind
  apply h at hfval'
  Hint (hidden := true)
  "[Hint w595i] Now that you've established a value in the image of $(a,c)$ with `{hfval'}`, you can choose a preimage with the required properties."
  choose b hb using hfval'
  use b
  grind

/---/
TheoremDoc intermediate_value_Ioo as "intermediate_value_Ioo" in "Topology"
NewTheorem intermediate_value_Ioo

Conclusion "Conclusion Rigi L09"
