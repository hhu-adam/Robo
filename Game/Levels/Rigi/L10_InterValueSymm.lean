import Game.Levels.Rigi.L09_InterValue

World "Rigi"
Level 10

Title ""



Introduction
"Intro Rigi L10: Intermediate value theorem has several variants, e.g.
```
intermediate_value_Ioo: Ioo (f a) (f c) ⊆ f '' Ioo a c
```
(as in previous level) and
```
intermediate_value_Ioo': Ioo (f c) (f a) ⊆ f '' Ioo a c
```
Which of these two to use depends on which of the two intervals $(f(a), f(c))$ and $(f(c), f(a))$ is non-empty, i.e. on whether `f a < f c` or `f c < f a`.
"

open Set

/-- If `f`, `f : ℝ → ℝ` is continuous and `a`, `c` (`a c : ℝ`) are points with `a < c` and
`f a > f c`, then there is some `b ∈ Ioo a c` with `f b > f c`. -/
TheoremDoc exists_mem_Ioo_val_gt_right as "exists_mem_Ioo_val_gt_right" in "Shade"

Statement exists_mem_Ioo_val_gt_right (preamble := grind_mode 1) {f : ℝ → ℝ} {a c : ℝ} (hf : Continuous f) (hac : a < c)
    (h_lt : f c < f a) : ∃ b ∈ Ioo a c, f b > f c := by
  have h : Set.Ioo (f c) (f a) ⊆ f '' Set.Ioo a c := by
    apply intermediate_value_Ioo'
    · grind
    · fun_prop
  have : (f c + f a) / 2 ∈ (Ioo (f c) (f a)) := by grind
  apply h at this
  choose b hb using this
  use b
  grind

/---/
TheoremDoc intermediate_value_Ioo' as "intermediate_value_Ioo'" in "Topology"
NewTheorem intermediate_value_Ioo'
