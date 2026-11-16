import Game.Levels.Rigi.L10_InterValueSymm

World "Rigi"
Level 11

Title ""

Introduction "Intro Rigi L11 (the boss): **Light and Shadow** (the *Rising Sun Lemma*)."

open Set

variable {f : ℝ → ℝ} {a c : ℝ}

Statement (preamble := grind_mode 1) (hf : Continuous f) (hac : a < c) (ha : a ∈ Sun f) (hc : c ∈ Sun f)
   (h_shade : ∀ b ∈ Set.Ioo a c, b ∈ Shade f) : f a = f c := by
  Hint (strict := true)
  "[Hint 0u20z] Let `f : ℝ → ℝ` be a continuous function.
  If `a` and `c` with `a < c` are in the sun,  but every `b` between a and c is in the shade, then `f a = f c`.
  Start by distinguishing the cases `f a < f c`, `f a = f c`, `f a > f c`.
  In the first and the last case, you will need to find a contradiction."
  obtain h_lt | h_eq | h_gt := lt_trichotomy (f a) (f c)
  · Hint (hidden := true)
    "[Hint sbosf] In this case, `a` is a shade point since `a < c` and `f a < f c`."
    have : a ∈ Shade f := by
      use c
    rw [← not_mem_Sun_iff_mem_Shade] at this
    contradiction
  · assumption
  · /- ---------------------------------------------------------------- -/
    /- Interesting case.  PART A:  Construction of s                    -/
    Hint (strict := true) "PART A: Construction of the supremum s

    One can find a `b` between `a`  and `c` with `f b > f c`.
    The set `Shaders f b` is non-empty, as b is in the shade,
    and it is bounded above by c, since c is in the sun with value smaller than at b.
    In particular, Shaders f b has some supremum `s`.

    So: First, prove that there is some `b ∈ Ioo a c` with this property."
    have this : ∃ b ∈ Ioo a c, f b > f c := by
      Hint "[Hint pbf] Remember the preceding level."
      apply exists_mem_Ioo_val_gt_right
      assumption
      grind
      grind
    obtain ⟨b, hb_mem, hfb⟩ := this
    Hint (strict := true)
    "[Hint hw34l] To construct the supremum of `Shaders f {b}`, you'll first want to show that the set is non-empty and that `c` is an upper bound."
    have h_ne : (Shaders f b).Nonempty := by
      Hint (hidden := true) "[Hint mwqb] Remember `shaders_nonempty`"
      apply shaders_nonempty
      apply h_shade
      assumption
    have hc_bounds : c ∈ upperBounds (Shaders f b) := by
      Hint (hidden := true) "[Hint dtpx] Remember `upperBounds_Shaders`"
      apply upperBounds_Shaders hc hfb
    Hint "[Hint 60ivz] Suggestion: `let s := sSup (Shaders f b)`"
    let s := sSup (Shaders f b)
    /- ------------------------------------------------- -/
    /- Intermezzo -/
    Hint (hidden := true)
    "[Hint mcvid] Establish that `b` is in the shade, and that `f b ≤ f s`."
    have hb : b ∈ Shade f := by
      apply h_shade at hb_mem
      assumption
    have hfb_le_fs : f b ≤ f s := by
      apply val_le_val_sSup_Shaders               -- learlier LEVEL
      · fun_prop
      · assumption
      · Hint "[Hint vfajy] Just `use` `c` (`use c`)."
        use c
    /- ------------------------------------------------- -/
    /- PART B:  s is in the Shade                        -/
    Hint (strict := true)
    "[Hint umu4r] The grand plan is now to show that on the one hand, `{s}` is in the shade, and on the other hand, s is in the sun.
    We start with the shade.  By our assumption `h_shade`, it suffices to show that s sits strictly between `a` and `c`.
    Proceed as follows:
    - `s ≤ c` in view of `{hc_bounds}`, and in fact
    - `s < c`.
    - `b < s`, and a fortiori
    - `a < s`
    "
    have s_le_c : s ≤ c := by
      apply csSup_le
      · assumption
      apply hc_bounds
    have s_lt_c : s < c := by
      grind
    have b_lt_s : b < s := by
      simp only [s]
      Hint (hidden := true) "[Hint cdp6] Remember `lt_sSup_Shaders`."
      apply lt_sSup_Shaders                       -- earlier LEVEL
      · assumption
      · use c
    have h_s : s ∈ Shade f := by
      apply h_shade
      grind
    /- ---------------------------------------------- -/
    /- PART C : s is in the Sun                       -/
    clear h_ne hb_mem hfb s_le_c s_lt_c b_lt_s
    Hint
    "On the other hand, `s` is in the sun.
    Start with `have : {s} ∈ Sun f`.
    "
    have : s ∈ Sun f := by
      simp [Sun]
      intro t ht
      Hint (hidden := true)
      "[Hint rsdov] You need to apply `val_le_of_sSup_Shaders_lt` to finish this.
      And to apply this, you'll need to establish `BddAbove (Shaders f b)`."
      have : BddAbove (Shaders f b) := by
        use c
      have h' := val_le_of_sSup_Shaders_lt hb this ht
      grind
    /- ---------------------------------------------- -/
    rw [← not_mem_Shade_iff_mem_Sun] at this
    contradiction

Conclusion "Conclusion Rigi L11"
