import Game.Metadata




import Game.Levels.MatrixSpan.L05

World "Span"
Level 8

Title "" -- "Span"

/- # Introduction

The universal property of the submodule `Submodule.span K S`  spanned by a set
`S : Set M` is that `x ∈ Submodule.span K S` iff `x ∈ P` for any submodule `P`
containing `S`.

-/

open Real Function Set Finset

/---/
TheoremDoc powers_commute as "powers_commute" in "LinearAlgebra"

Statement powers_commute {n : ℕ} {A : Mat[n,n][ℝ]} (X Y : Mat[n,n][ℝ])
    (hX : X ∈ Submonoid.powers A) (hY : Y ∈ Submonoid.powers A) : X * Y = Y * X := by
  rw [Submonoid.mem_powers_iff] at *
  obtain ⟨m, rfl⟩ := hX
  obtain ⟨n, rfl⟩ := hY
  rw [← pow_add, ← pow_add, add_comm]

/---/
TheoremDoc pow_add as "pow_add" in "+ *"

/---/
TheoremDoc Submonoid.mem_powers_iff as "Submonoid.mem_powers_iff" in "LinearAlgebra"

NewTheorem pow_add Submonoid.mem_powers_iff
TheoremTab "LinearAlgebra"
