import Game.Metadata

World "Quotient"
Level 7

Title "When Is Quotient Lift Surjective"

Introduction
"
In the previous level we explained that for a setoid on a type `B`, the universal property of
the quotient construction induces for every function `A → B` a function `Quotient.lift` such that
`Quotient.lift f ⟦a⟧ = f a` for all `a : A`.

In diagramatic terms this means that the following diagram commutes:
... draw a tikz diagram here:
A pointing to B via the arrow labeled f
A pointing to Quotient A via the arrow labeled Quotient.mk
There's a dashed arrow labeled Quotient.lift f going from Quotient A to B.

"

open Function List Sym Quotient

#check Quot.surjective_lift


Statement Quotinet.surjective_lift {A B : Type*} (s : Setoid A) {f : A → B}
    (f_resp_rel : ∀ a₁ a₂, a₁ ≈ a₂ → f a₁ = f a₂) :
    Function.Surjective (Quotient.lift f f_resp_rel) ↔ Function.Surjective f := by
  constructor
  · intro h
    rw [← Quotient.lift_comp_mk f]
    apply h.comp
    apply surjective_quotient_mk'
    done
  · intro h
    apply Surjective.of_comp (g:= Quotient.mk s)
    simp [h]


NewTheorem Quotient.lift_comp_mk surjective_quotient_mk'
TheoremTab "Quotient"
