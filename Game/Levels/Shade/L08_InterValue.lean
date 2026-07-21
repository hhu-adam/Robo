import Game.Levels.Shade.L07_ValLeValSSupShaders

World "Shade"
Level 8

Title ""

Introduction
"[Intro]
 If a continuous function `f` takes a strictly larger value at the left endpoint `a` than at the
 right endpoint `b` of an interval, then somewhere strictly between the endpoints the function still
 exceeds its value at that right endpoint.
"
/- TODO
Add natural-language summary of the statement.

*Comment resolved (Wenrong):* added an `[Intro]` natural-language summary of the statement above.
-/

/- TODO
This level looks quite independent of everything else.
- Move it right before Boss.
- Add a second intermediate value exercise level, e.g.
  a symmetric version of this level with f a < f b.

*Comment resolved (Wenrong):* moved this level to just before the Boss (now level 4), and added a
symmetric version (`f a < f b`) as the following level, `L05_InterValueSymm`. That level is left
without hints on purpose, so the player practises the same argument unaided.
-/

open Set FullGrind

/-- If `f` is continuous on `[a, b]` with `a < b` and `f a > f b`, then there is some
`s ∈ Ioo a b` with `f s > f b`. -/
TheoremDoc exists_mem_Ioo_gt as "exists_mem_Ioo_gt" in "Shade"

Statement exists_mem_Ioo_gt {f : ℝ → ℝ} {a b : ℝ} (hf : Continuous f) (hab : a < b)
    (h_lt : f b < f a) : ∃ s ∈ Ioo a b, f s > f b := by
  Hint "[Hint ivIoo] Perhaps, you should first prove `Set.Ioo (f b) (f a) ⊆ f '' Set.Ioo a b`."
  have h : Set.Ioo (f b) (f a) ⊆ f '' Set.Ioo a b := by
    Hint "[Hint itvIoo] First, apply the theorem `intermediate_value_Ioo'`."
    apply intermediate_value_Ioo'
    · grind
    Hint "The remaining goal is the continuity statement `Continuous f`. Use `fun_prop`,
      which automatically proves such function properties."
    · fun_prop
  Hint "[Hint Ioontps] Since `f b < f a`, then we have that `(Ioo (f b) (f a)).Nonempty`."
  have hs : (Ioo (f b) (f a)).Nonempty := by
    use (f b + f a) / 2
    grind
  obtain ⟨z, hz⟩ := hs
  obtain h1 := h hz
  choose x hx using h1
  use x
  grind

/-- -/
TheoremDoc intermediate_value_Ioo' as "intermediate_value_Ioo'" in "Topology"
NewTheorem intermediate_value_Ioo'
