import Game.Metadata
import Game.Levels.SymmSquare.L10
import Game.Levels.SymmSquare.L08
import Game.Levels.SymmSquare.L05_QuotientExistsRep

World "Symmetric Square"
Level 11

Introduction "Intro Symm L11"

open Function Sym

attribute [local instance] Sym2.Rel.setoid

noncomputable section

Statement Sym2.liftEquiv {A B : Type*} :
    (Sym2 A → B) ≃ { f : A → A → B | ∀ a₁ a₂, f a₁ a₂ = f a₂ a₁ } := by
  Hint "[Hint s11univ] The two previous constructions are inverse to each other: restricting a
    function on unordered pairs to two arguments, and lifting a symmetric function of two
    arguments along `⟦·⟧` with `Quotient.lift f ⟦a⟧ = f a`. Assembling them shows that `Sym2 A`
    is exactly what classifies symmetric functions in two arguments."
  Hint "[Hint s11tmpl] An equivalence consists of four fields: the two maps `toFun` and
    `invFun`, plus the proofs `left_inv` and `right_inv` that they undo each other. The template
    ```
    refine' \{ toFun f := _, invFun g := _, left_inv := _, right_inv := _}
    ```
    leaves you exactly those four holes."
  Hint (hidden := true) "[Hint s11fg] The two maps are `Sym_f` and `Sym_g` from the previous
    levels. Mind that `toFun` lands in a subtype, so it has to carry the symmetry proof
    `Sym_f_swap` along."
  refine' { toFun f := ⟨Sym_f f, Sym_f_swap f⟩, invFun g := Sym_g g, left_inv := _, right_inv := _}
  · simp [LeftInverse]
    intro f
    ext q
    obtain ⟨p, hp⟩ := Quotient.exists_rep q
    rw [← hp]
    rfl
  · simp [RightInverse, LeftInverse]
    intro f
    rfl

TheoremTab "Quotient"
