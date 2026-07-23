import Game.Levels.Shade.L10_InterValueSymm

World "Shade"
Level 11

Title ""

Introduction "Intro Shade L11 (the boss): **Light and Shadow** (the *Rising Sun Lemma*).

> Let `f : ℝ → ℝ` be a continuous function. If `a` and `c` with `a < c` are
> themselves not shadow points, but every `s` between `a` and `c` is a shadow point, then `f a = f c`.

In the game, `s ∈ Shade f` means exactly that `s` is a shadow point. The hypotheses say the open
interval `(a, c)` consists entirely of shadow points while the endpoints `a` and `c` are not, and
the goal is `f a = f c`.

**The mathematical idea.** Compare `f a` and `f c` by trichotomy.

* If `f a < f c`: then `c` itself is a point to the right of `a` with a larger value, so `a` would be
  a shadow point — contradicting `a ∈ Sun f`.

* If `f a = f c`: there is nothing to prove.

* If `f a > f c`: we derive a contradiction. One can find a `b` between `a`
  and `c` with `f b > f c`.   The set `Shaders f b` is non-empty, as `b` is in the shade,
  and it is bounded above by `c`, since `c` is in the sun with value smaller than at `b`.
  In particular, the supremum `s` of `Shaders f b` is `≤ c`.

  Also, trivially/by some eralier lemma `b ≤ s` by earlier lemma, so we have $s ∈ Ioc a c$.

  By definition of `Shaders f b`, for all points in `Shaders f b`, `f` takes a value at least `f b`.
  Thus, by an an analogous argument to Boss of Aquarium, `f s ≥ f b`.
  This implies, in particular, that `s ≠ c`.
  So `d ∈ Ioo (a b)`.  By our assumptions, this implies that `d` is in the shade.

  On the other hand, to the right of `d`, the function remains below `f c` – that is what `d` being
  the supremum means.  A fortiori, given that `f d ≥ f c`, the function remains below `f c`.
  So `d` is in the sun.

  Contradiction.
"

open Set FullGrind

variable {f : ℝ → ℝ} {a c : ℝ}

Statement (hf : Continuous f) (hac : a < c) (ha : a ∈ Sun f) (hc : c ∈ Sun f)
   (h_shade : ∀ b ∈ Set.Ioo a c, b ∈ Shade f) : f a = f c := by
  obtain h_lt | h_eq | h_gt := lt_trichotomy (f a) (f c)
  · Hint "[Hint sbosf] In this case, `a` is a shade point since `a < c` and `f a < f c`."
    have : a ∈ Shade f := by
      use c
    rw [← not_mem_Sun_iff_mem_Shade] at this
    contradiction
  · assumption
  · /- ---------------------------------------------------------------- -/
    /- Interesting case.  PART A:  Construction of s                    -/
    Hint "First, we prove that there is a `b ∈ Ioo a c`, such that `f b > f c`. "
    have this : ∃ b ∈ Ioo a c, f b > f c := by
      Hint "[Hint pbf] Remember the proof before."
      apply exists_mem_Ioo_gt
      assumption
      grind
      grind
    obtain ⟨b, hb_mem, hfb⟩ := this
    have h_ne : (Shaders f b).Nonempty := by
      Hint (hidden := true) "[Hint mwqb] Remember `shaders_nonempty`"
      apply shaders_nonempty
      apply h_shade
      assumption
    have hc : c ∈ upperBounds (Shaders f b) := by
      Hint (hidden := true) "[Hint dtpx] Remember `upperBounds_Shaders`"
      apply upperBounds_Shaders hc hfb
    have h_bdd : BddAbove (Shaders f b) := by
      use c
    let s := sSup (Shaders f b)
    /- ------------------------------------------------- -/
    /- PART B:  s is in the Shade                        -/
    have hb : b ∈ Shade f := by
      apply h_shade at hb_mem
      assumption
    have s_le_c : s ≤ c := by
      apply csSup_le
      · assumption
        apply hc
    have hfb_le_fs : f b ≤ f s := by
      apply val_le_val_sSup_Shaders               -- learlier LEVEL
      · fun_prop
      · assumption
      · assumption
    have b_lt_s : b < s := by
      simp only [s]
      apply lt_sSup_Shaders                       -- earlier LEVEL
      · assumption
      · assumption
    have h_s : s ∈ Shade f := by
      apply h_shade
      grind
    /- ---------------------------------------------- -/
    /- PART C : d is in the Sun                       -/
    have lt_aux : ∀ x, s < x → f s ≤ f b := by
      intro x hx
      apply val_le_of_sSup_Shaders_lt hb h_bdd x hx  -- earlier LEVEL
    have : d ∈ Sun f := by
      simp [Sun]
      intro t ht
      grind
    /- ---------------------------------------------- -/
    rw [← not_mem_Shade_iff_not_mem_Sun] at h_shade
    contradiction
