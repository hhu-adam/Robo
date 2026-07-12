import Game.Metadata

World "Uncountable"
Level 3

noncomputable section

open Function Cardinal

/- Introduce `Cardinal.mk_congr` inn this level. -/
Statement : #ℤ = ℵ₀ := by
  have : #ℕ = ℵ₀ := by
    apply mk_nat
  rw [← this]
  apply Cardinal.mk_congr
  Hint "[Hint nequivZ] Remember the proof in the first level. "
  symm
  let f : ℕ → ℤ := fun n ↦ if Even n then n / 2 else - (n + 1) / 2
  have : Bijective f := by
    constructor
    · intro x y hxy
      grind
    · intro x
      by_cases! h : 0 ≤ x
      · use (2 * x.toNat)
        grind
      · use (- 2 * x).toNat - 1
        grind
  apply Equiv.ofBijective f
  assumption

/---/
TheoremDoc Cardinal.mk_congr as "Cardinal.mk_congr" in "Cardinal"

NewTheorem Cardinal.mk_congr
