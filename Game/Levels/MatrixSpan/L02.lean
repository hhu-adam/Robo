import Game.Metadata

World "Span"
Level 2

Introduction
"Intro Span L02:
Let $R$ be a ring and $M$ be an $R$-module. A submodule $N$ of $M$ is a subset that is closed under
addition and scalar multiplication.

Let's now focus on modules over `ℝ`. Given an `ℝ`-module $M$ and a submodule $N$, let $r$ be a
nonzero real number. Then `r • x` belongs to $N$ if and only if $x$ belongs to $N$.
"

open Real Function Set Finset

Statement (M : Type*) [AddCommMonoid M] [Module ℝ M] (N : Submodule ℝ M) (x : M) (r : ℝ)
    (hr : r ≠ 0) : r • x ∈ N ↔ x ∈ N := by
  Hint (hidden := true) "[Hint sp2ctsp] First use `constructor` to split into two goals. "
  constructor
  · intro hrxS
    Hint (strict := true) "[Hint sp2rinv] Since `r` is nonzero, then `r` is invertible in `ℝ`, i.e.
      there is an element `s` such that `s * r = 1`. "
    Hint (strict := true) (hidden := true) "[Hint sp2exsv] Establish `∃ s, s * r = 1` by `have`."
    have : ∃ s, s * r = 1 := by
      Hint (hidden := true) "[Hint sp2iuei] Note that the theorem `isUnit_iff_exists_inv'`."
      apply isUnit_iff_exists_inv'.mp
      Hint "[Hint sp2nzun] An real number is unit if and only if it is nonzero. This theorem is `Ne.isUnit`."
      apply Ne.isUnit hr
    Hint (hidden := true) "[Hint sp2obtv] You can pick the inverse of `r` by `obtain ⟨·, ·⟩ := {this}`."
    obtain ⟨s, hs⟩ := this
    Branch
      -- alternative proof
      have aux : s • (r • x) ∈ N := by
        apply Submodule.smul_mem
        assumption
      rw [smul_smul, hs, one_smul] at aux
      assumption
    Hint "[Hint sp2sfcs] It suffices to prove `(1 : ℝ) • x ∈ N`."
    suffices h : (1 : ℝ) • x ∈ N
    · Hint "[Hint sp2onsm] Remember the definition of module, for any element `x ∈ N`, `1 • x = x`. This is `one_smul`."
      Hint (hidden := true) "[Hint sp2rwos] Rewrite `one_smul` at {h}. "
      rw [one_smul] at h
      assumption
    rw [← hs]
    Hint "[Hint sp2smsm] Let `M` be an `R`-module, let `r, s` be two elements in R and let `x` be an element in
      M, then we have that `r • s • x = (r * s) • x`. This is `smul_smul`. "
    Hint (hidden := true) "[Hint sp2rwsm] Rewrite `smul_smul` backwards."
    rw [← smul_smul]
    Hint (hidden := true) "[Hint sp2smmb] Let `M` be an `R`-module and `N` be submodule of `M`, let `r` be an
      element in R and let `x` be an element in M, if `x` belongs to N, then so does `r • x`.
      This is `Submodule.smul_mem`."
    apply Submodule.smul_mem
    assumption
  · intro h
    Hint (hidden := true) "[Hint sp2rsmm] Remember the theorem `Submodule.smul_mem`."
    apply Submodule.smul_mem
    assumption

/---/
TheoremDoc Submodule.smul_mem as "Submodule.smul_mem" in "LinearAlgebra"

/---/
TheoremDoc isUnit_iff_exists_inv as "isUnit_iff_exists_inv" in "ℝ"

/---/
TheoremDoc isUnit_iff_exists_inv' as "isUnit_iff_exists_inv'" in "ℝ"

/---/
TheoremDoc Ne.isUnit as "Ne.isUnit" in "ℝ"

NewTheorem Submodule.smul_mem isUnit_iff_exists_inv isUnit_iff_exists_inv' Ne.isUnit
