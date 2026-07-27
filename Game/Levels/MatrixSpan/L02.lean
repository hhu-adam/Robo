import Game.Metadata

World "Span"
Level 2

Introduction
"
Let $R$ be a ring and $M$ be an $R$-module. A submodule $N$ of $M$ is a subset that is closed under
addition and scalar multiplication.

Let's now focus on modules over `ℝ`. Given an `ℝ`-module $M$ and a submodule $N$, let $r$ be a
nonzero real number. Then `r • x` belongs to $N$ if and only if $x$ belongs to $N$.
"

open Real Function Set Finset

Statement (M : Type*) [AddCommMonoid M] [Module ℝ M] (N : Submodule ℝ M) (x : M) (r : ℝ)
    (hr : r ≠ 0) : r • x ∈ N ↔ x ∈ N := by
  constructor
  · intro hrxS
    have : ∃ s, s * r = 1 := by
      apply isUnit_iff_exists_inv'.mp
      apply Ne.isUnit hr
    obtain ⟨s, hs⟩ := this
    have aux : s • (r • x) ∈ N := by
      apply Submodule.smul_mem
      assumption
    rw [smul_smul, hs, one_smul] at aux
    assumption
  · intro h
    apply Submodule.smul_mem
    assumption

/---/
TheoremDoc Submodule.smul_mem as "Submodule.smul_mem" in "LinearAlgebra"

/---/
TheoremDoc inv_smul_smul as "inv_smul_smul" in "LinearAlgebra"

/---/
DefinitionDoc Units.mk0 as "Units.mk0" in "LinearAlgebra"

NewTheorem Submodule.smul_mem inv_smul_smul
NewDefinition Units.mk0
