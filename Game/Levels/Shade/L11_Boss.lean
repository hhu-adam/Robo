import Game.Levels.Shade.L10_ShadeSetBddAbove

World "Shade"
Level 11

Title ""

Introduction "Intro Shade L11 (the boss): **Light and Shadow** (the *Rising Sun Lemma*).

> Let `f : ℝ → ℝ` be a continuous function. A real number `s` is called a *shadow point* of `f` if
> there exists a real number `t` with `t > s` and `f t > f s`. If `a` and `b` with `a < b` are
> themselves not shadow points, but every `s` between `a` and `b` is a shadow point, then `f a = f b`.

In the game, `s ∈ Shade f` means exactly that `s` is a shadow point. The hypotheses say the open
interval `(a, b)` consists entirely of shadow points while the endpoints `a` and `b` are not, and
the goal is `f a = f b`.

**The mathematical idea.** Compare `f a` and `f b` by trichotomy.

* If `f a < f b`: then `b` itself is a point to the right of `a` with a larger value, so `a` would be
  a shadow point — contradicting `a ∉ Shade f`.

* If `f a = f b`: there is nothing to prove.

* If `f a > f b`: we derive a contradiction. One can find a `c` between `a`
  and `b` with `f c > f b`. Now consider the supremum `d` of the set
  `shadeSet f c b = {t ∈ (c, b) | f c ≤ f t}`. By continuity the value at `d` is still at least `f c`
  (so `f d ≥ f c > f b`), and `d` lies strictly inside `(a, b)`. On one hand `d ∈ (a, b)` forces `d`
  to be a shadow point. On the other hand, just past `d` the function never climbs back to `f c`
  (that is what `d` being the supremum means), and beyond `b` it stays below `f b < f c`; so no point
  to the right of `d` exceeds `f d` — meaning `d` is *not* a shadow point. This contradiction rules
  out `f a > f b`, leaving `f a = f b`.

"

open Set FullGrind

variable {f : ℝ → ℝ} {a b : ℝ}

Statement (hf : Continuous f) (hab : a < b) (ha : a ∉ Shade f) (hb : b ∉ Shade f)
   (h₀ : ∀ k ∈ Set.Ioo a b, k ∈ Shade f) : f a = f b := by
  obtain h_lt | h_eq | h_gt := lt_trichotomy (f a) (f b)
  · Hint "[Hint sbosf] In this case, `a` is a shade point since `a < b` and `f a < f b`."
    have : a ∈ Shade f := by
      use b
    contradiction
  · assumption
  · Hint "First, we prove that there is a `c ∈ Ioo a b`, such that `f c > f b`. "
    have hc : ∃ c ∈ Ioo a b, f c > f b := by
      Hint "[Hint pbf] Remember the proof before."
      apply exists_mem_Ioo_gt hf hab h_gt
    obtain ⟨c, hc_mem, hfc⟩ := hc
    let d := sSup (shadeSet f c b)
    have hn : (shadeSet f c b).Nonempty := by
      apply shadeSet_nonempty hb hfc
      apply h₀
      assumption
    have hbd : BddAbove (shadeSet f c b) := by
      Hint "[Hint] Remember the proof before."
      use b
      intro y hy
      unfold shadeSet at hy
      grind
    have d_le : d ≤ b := by
      apply csSup_le
      · assumption
      unfold shadeSet
      grind
    have hfc_le_fd : f c ≤ f d := by
      have hsub : (shadeSet f c b) ⊆ {x | f c ≤ f x} := sep_subset_setOf _ _
      apply closure_minimal hsub
      · apply isClosed_le
        · fun_prop
        · fun_prop
      · apply csSup_mem_closure
        · assumption
        · assumption
    have c_lt_d : c ≤ d := by
      obtain ⟨x, hx⟩ := hn
      have : x ≤ d := by
        apply le_csSup
        · assumption
        · assumption
      unfold shadeSet at hx
      grind
    have d_lt : d < b := by
      grind
    have lt_aux₁ : ∀ x, b < x → f x ≤ f b := by
      apply not_mem_shade
      assumption
    have lt_aux₂ : ∀ x, x ∈ Ioo d b → f x ≤ f c := by
      intro x hx
      obtain ⟨hx1, hx2⟩ := hx
      have not_mem : x ∉ shadeSet f c b := by
        apply notMem_of_csSup_lt
        · assumption
        apply shadeSet_bddAbove f c b
      by_contra hc
      have mem_aux : x ∈ shadeSet f c b := by
        unfold shadeSet
        grind
      contradiction
    have : d ∉ Shade f := by
      by_contra hc
      obtain ⟨t, ht⟩ := hc
      grind
    have : d ∈ Shade f := by
      apply h₀
      grind
    contradiction

/-- -/
TheoremDoc Set.sep_subset_setOf as "sep_subset_setOf" in "Set"

/-- -/
TheoremDoc notMem_of_csSup_lt as "notMem_of_csSup_lt" in "sSup"

NewTheorem Set.sep_subset_setOf notMem_of_csSup_lt
