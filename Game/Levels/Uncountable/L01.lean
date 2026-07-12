import Game.Metadata

World "Uncountable"
Level 1

noncomputable section

open Function

/---/
TheoremDoc nat_equiv_int as "nat_equiv_int" in "Cardinal"

Statement nat_equiv_int : ℕ ≃ ℤ := by
  Hint "[Hint eofBij] First construct a bijection and use the theorem
    `Equiv.ofBijective`"
  let f : ℕ → ℤ := fun n ↦ if Even n then n / 2 else - (n + 1) / 2
  have : Bijective f := by
    -- let g : ℤ → ℕ := fun
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
DefinitionDoc Equiv.ofBijective as "Equiv.ofBijective" in "Function"

NewDefinition Equiv.ofBijective

-- TODO: add TacticDoc for `by_cases!`
NewTactic by_cases!
