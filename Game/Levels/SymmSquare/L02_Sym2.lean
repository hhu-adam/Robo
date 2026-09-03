import Game.Metadata


World "Symmetric Square"
Level 2

Introduction "Intro Symm L02"

open Sym2

attribute [local instance] Sym2.Rel.setoid

/- Two pairs are related by `Sym2.Rel` if they are permutations of each other. -/

Statement Sym2.pair_rel_iff {A : Type*} {x y z w : A} : (x, y) ≈ (z, w) ↔ x = z ∧ y = w ∨ x = w ∧ y = z := by
  Hint "[Hint sy2set] A *setoid* on a type is nothing but an equivalence relation on it,
    written `a ≈ b` (typed `\\~~` or `\\approx`). Since `Sym2.Rel A` is an equivalence relation,
    it makes `A × A` into a setoid, and `(x, y) ≈ (z, w)` says the two pairs are permutations
    of each other."
  Hint (hidden := true) "[Hint sy2ctr] The goal is an `↔`, so split it with `constructor`."
  constructor
  · intro h
    Hint (hidden := true) "[Hint sy2cs] `{h}` can only come from `refl` or from `swap`, and
      `cases` gives you exactly those two possibilities."
    cases h
    · grind
    · grind
  · intro h
    cases h
    · rw [h_1.1, h_1.2]
    · rw [h_1.1, h_1.2]
      apply Sym2.Rel.swap

NewDefinition Setoid

TheoremTab "Quotient"
