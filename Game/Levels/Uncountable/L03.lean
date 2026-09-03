import Game.Metadata

World "Uncountable"
Level 3

Introduction "Intro Uncountable L03"

noncomputable section

open Function Cardinal FullGrind

/- Introduce `Cardinal.mk_congr` inn this level. -/
Statement : #ℤ = ℵ₀ := by
  Hint (strict := true) "[Hint hnqz] In the previous level you saw that the cardinality of
    `ℕ` is `ℵ₀`. Make that fact available here with a `have`."
  have : #ℕ = ℵ₀ := by
    apply mk_nat
  Hint (strict := true) "[Hint dwrp] Rewriting backwards with `{this}` leaves you with
    `#ℤ = #ℕ`. Two types have the same cardinality as soon as there is a bijection
    between them — that is what `Cardinal.mk_congr` says."
  rw [← this]
  apply Cardinal.mk_congr
  Hint "[Hint nequivZ] First use `symm` to reflect the direction of equivalence.
    Remember the proof in the first level. "
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
