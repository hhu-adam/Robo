import Game.Metadata

World "Uncountable"
Level 1

Introduction "Intro Uncountable L01"

noncomputable section

open Function FullGrind

/---/
DefinitionDoc nat_equiv_int as "nat_equiv_int" in "Cardinal"

/---/
TheoremDoc nat_equiv_int as "nat_equiv_int" in "Cardinal"

Statement nat_equiv_int : ℕ ≃ ℤ := by
  Hint "[Hint eofBij] First construct a bijection and use the theorem
    `Equiv.ofBijective`"
  Hint (hidden := true) "[Hint vqmr] Consider the following function:
    $$
    f(n) = \\begin\{cases}
    n / 2 & n \\text\{ even},  \\\\ %(new line)
    -(n+1) / 2 & n \\text\{ odd}.
    \\end\{cases}
    $$
    "
  let f : ℕ → ℤ := fun n ↦ if Even n then n / 2 else - (n + 1) / 2
  have : Bijective f := by
    constructor
    · intro x y hxy
      grind
    · intro x
      Hint "[Hint vzdh] Which natural number is sent to `{x}`? Whether it is an even or an
        odd one depends on the sign of {x}, so discuss the two cases with `by_cases!`."
      by_cases! h : 0 ≤ x
      · Hint (hidden := true) "[Hint kmtr] The even numbers cover the non-negative
          integers: `use (2 * {x}.toNat)`."
        use (2 * x.toNat)
        grind
      · Hint (hidden := true) "[Hint pqjs] Now it has to be an odd number:
          `use ((- 2 * {x}).toNat - 1)`."
        use (- 2 * x).toNat - 1
        grind
  apply Equiv.ofBijective f
  assumption

NewDefinition Equiv.ofBijective
