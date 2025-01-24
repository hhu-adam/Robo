import Game.Metadata

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

import Game.Levels.MatrixSpan.L14

World "Span"
Level 15

Title "Span"

/- # Introduction

The universal property of the submodule `Submodule.span K S`  spanned by a set
`S : Set M` is that `x ∈ Submodule.span K S` iff `x ∈ P` for any submodule `P`
containing `S`.

-/

open Real Function Set Finset BigOperators

lemma powers_span_commute {n : ℕ} {A : Mat[n,n][ℝ]}
    {X Y : Mat[n,n][ℝ]} (hX : X ∈ Submodule.span ℝ (Submonoid.powers A))
    (hY : Y ∈ Submodule.span ℝ (Submonoid.powers A))
    : X * Y = Y * X := by
  fapply Submodule.span_induction₂ hX hY
  · intro B hB C hC
    apply powers_commute B C hB hC
  · intro Z
    simp
  · intro Z
    simp
  · intro D E F hDF hEF
    rw [add_mul, mul_add]
    simp [hDF, hEF]
  . sorry
  · sorry
  · sorry
