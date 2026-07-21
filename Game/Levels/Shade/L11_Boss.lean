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
  a shadow point — contradicting `a ∈ Sun f`.

* If `f a = f b`: there is nothing to prove.

* If `f a > f b`: we derive a contradiction. One can find a `c` between `a`
  and `b` with `f c > f b`.   The set `Shaders f c` is non-empty, as `c` is in the shade,
  and it is bounded above by `b`, since `b` is in the sun with value smaller than at `c`.
  In particular, the supremum `d` of `Shaders f c` is `≤ b`.

  Also, `c < d` by some triviality …, so `a < d`.

  By definition of `Shaders f c`, for all points in `Shaders f c`, `f` takes a value at least `f c`.
  Thus, by earlier levels …… `f d ≥ f c`.  This implies, in particular, that `d ≠ b`.
  So `d ∈ Ioo (a b)`.  By our assumptions, this implies that `d` is in the shade.

  On the other hand, to the right of `d`, the function remains below `f c` – that is what `d` being
  the supremum means.  A fortiori, given that `f d ≥ f c`, the function remains below `f c`.
  So `d` is in the sun.

  Contradiction.
"

open Set FullGrind

variable {f : ℝ → ℝ} {a b : ℝ}

Statement (hf : Continuous f) (hab : a < b) (ha : a ∈ Sun f) (hb : b ∈ Sun f)
   (h₀ : ∀ k ∈ Set.Ioo a b, k ∈ Shade f) : f a = f b := by
  obtain h_lt | h_eq | h_gt := lt_trichotomy (f a) (f b)
  · Hint "[Hint sbosf] In this case, `a` is a shade point since `a < b` and `f a < f b`."
    have : a ∈ Shade f := by
      use b
    rw [mem_Shade_iff_not_mem_Sun] at this
    contradiction
  · assumption
  · /- ---------------------------------------------------------------- -/
    /- Interesting case.  PART A:  Construction of d                    -/
    Hint "First, we prove that there is a `c ∈ Ioo a b`, such that `f c > f b`. "
    have hc : ∃ c ∈ Ioo a b, f c > f b := by
      Hint "[Hint pbf] Remember the proof before." -- THIS SHOUD BE REPEATET!
      apply exists_mem_Ioo_gt hf hab h_gt
    obtain ⟨c, hc_mem, hfc⟩ := hc
    have h_ne : (Shaders f c).Nonempty := by
      Hint (hidden := true) "[Hint mwqb] Remember `shaders_nonempty`"
      apply shaders_nonempty
      apply h₀
      assumption
    have h_b : b ∈ upperBounds (Shaders f c) := by
      Hint (hidden := true) "[Hint dtpx] Remember `upperBounds_Shaders`"
      apply upperBounds_Shaders hb hfc
    have h_bdd : BddAbove (Shaders f c) := by
      use b
    let d := sSup (Shaders f c)
    /- ------------------------------------------------- -/
    /- PART B:  d is in the Shade                        -/
    have h_c : c ∈ Shade f := by
      apply h₀ at hc_mem
      assumption
    have d_le_b : d ≤ b := by
      apply csSup_le --(h₂ := hbd)
      · assumption
      · -- OPTIONAL:
        -- unfold upperBounds at hbd
        -- OR:
        -- rw [mem_upperBounds] at hbd
        apply h_b
    have hfc_le_fd : f c ≤ f d := by              -- learlier LEVEL
      apply val_le_val_sSup_Shaders
      · fun_prop
      · assumption
      · assumption
    have c_lt_d : c < d := by
      simp only [d]
      apply lt_sSup_Shaders                       -- earlier LEVEL
      · assumption
      · assumption
    have h_shade : d ∈ Shade f := by
      apply h₀
      grind
    /- ---------------------------------------------- -/
    /- PART C : d is in the Sun                       -/
    have lt_aux : ∀ x, d < x  → f x ≤ f c := by -- another LEVEL about Shaders?
      intro x hx
      have not_mem : x ∉ Shaders f c := by
        apply notMem_of_csSup_lt                -- ADDITIONAL LEMMA used here!
        · assumption
        · assumption
      unfold Shaders at not_mem
      grind
    have : d ∈ Sun f := by
      simp_log [Sun]
      intro t ht
      grind
    /- ---------------------------------------------- -/
    rw [mem_Shade_iff_not_mem_Sun] at h_shade
    contradiction

/-- -/
TheoremDoc Set.sep_subset_setOf as "sep_subset_setOf" in "Set"

/-- -/
TheoremDoc notMem_of_csSup_lt as "notMem_of_csSup_lt" in "sSup"

NewTheorem Set.sep_subset_setOf notMem_of_csSup_lt
