import Game.Levels.Shade.L10_InterValueSymm

World "Shade"
Level 11

Title ""

Introduction "Intro Shade L11 (the boss): **Light and Shadow** (the *Rising Sun Lemma*).

> Let `f : ℝ → ℝ` be a continuous function. If `a` and `c` with `a < c` are in the sun,
but every `b` between a and c is in the shade, then `f a = f c`."

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
    Hint "**The mathematical idea.**

    We derive a contradiction. One can find a `b` between `a`  and `c` with `f b > f c`.
    The set `Shaders f b` is non-empty, as `b` is in the shade,
    and it is bounded above by `c`, since `c` is in the sun with value smaller than at `b`.
    In particular, the supremum `s` of `Shaders f b` is `≤ c`.

    Also, trivially/by some eralier lemma `b ≤ s` by earlier lemma, so we have `s ∈ Ioc a c`.

    By definition of `Shaders f b`, for all points in `Shaders f b`, `f` takes a value at least `f b`.
    Thus, by an an analogous argument to Boss of Aquarium, `f s ≥ f b`.
    This implies, in particular, that `s ≠ c`.
    So `s ∈ Ioo a c`.  By our assumptions, this implies that `s` is in the shade.

    On the other hand, to the right of `s`, the function remains below `f b` – that is what `s` being
    the supremum means.  A fortiori, given that `f s ≥ f b`, the function remains below `f s`.
    So `s` is in the sun.  CONTRADICTION.

    So: First, prove that there is some `b ∈ Ioo a c`, such that `f b > f c`."
    have this : ∃ b ∈ Ioo a c, f b > f c := by
      Hint "[Hint pbf] Remember the proof before."
      apply exists_mem_Ioo_val_gt_right
      assumption
      grind
      grind
    obtain ⟨b, hb_mem, hfb⟩ := this
    Hint "To construct the supremum of `Shaders f {b}`, you'll first want to show that the set
      is non-empty and that b is an upper bound."
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
    Hint (strict := true) (hidden := true) "[Hint 60ivz] Suggestion: `let s := sSup (Shaders f b)`"
    let s := sSup (Shaders f b)
    /- ------------------------------------------------- -/
    /- PART B:  s is in the Shade                        -/
    Hint (strict := true) (hidden := true) "[Hint umu4r] Suggestion: Work towards `{s} ∈ Shade f`
      First establish `b ∈ Shade f`."
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
    /- PART C : s is in the Sun                       -/
    clear h_ne hc hb_mem hfb
    Hint (hidden := true) "[Hint rsdov] Almost there …  You'll probably need
      `val_le_of_sSup_Shaders_lt` to finish this."
    have h_right_lt : ∀ t, s < t → f t ≤ f b := by
      intro x hx
      apply val_le_of_sSup_Shaders_lt
      · assumption
      · assumption
      · grind
    have : s ∈ Sun f := by
      simp [Sun]
      intro t ht
      grind
    /- ---------------------------------------------- -/
    rw [← not_mem_Shade_iff_mem_Sun] at this
    contradiction
