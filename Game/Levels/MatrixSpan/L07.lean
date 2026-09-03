import Game.Metadata
import Game.Levels.MatrixSpan.L04

World "Span"
Level 7

Introduction "Intro Span L07"

open Real Function Set Finset

/---/
TheoremDoc powers_commute as "powers_commute" in "LinearAlgebra"

Statement powers_commute {n : ℕ} {A : Mat[n,n][ℝ]} (X Y : Mat[n,n][ℝ])
    (hX : X ∈ Submonoid.powers A) (hY : Y ∈ Submonoid.powers A) : X * Y = Y * X := by
  Hint "[Hint sp7pows] `X` and `Y` are powers of the same matrix `A`, so both products are
    a power of A again — and adding exponents is commutative. Start by making those
    exponents visible."
  Hint (hidden := true) "[Hint sp7memp] `Submonoid.mem_powers_iff` turns membership into
    the existence of an exponent. Rewrite it at {hX} and {hY}."
  rw [Submonoid.mem_powers_iff] at hX hY
  Hint "[Hint sp7obtn] Take the two exponents apart with `obtain`."
  obtain ⟨m, hX₁⟩ := hX
  obtain ⟨n, hY₁⟩ := hY
  rw [← hX₁, ← hY₁, ← pow_add, ← pow_add, add_comm]

/--
Let `M` be a Monoid and let `n, m` be natural number, `a` be an element in `M`, then
`a ^ (m + n) = a ^ m * a ^ n`
-/
TheoremDoc pow_add as "pow_add" in "+ *"

/---/
TheoremDoc Submonoid.mem_powers_iff as "Submonoid.mem_powers_iff" in "LinearAlgebra"

NewTheorem pow_add Submonoid.mem_powers_iff
TheoremTab "LinearAlgebra"
