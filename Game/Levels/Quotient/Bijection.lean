import Game.Metadata
import Game.Metadata.StructInstWithHoles

import Game.Levels.Quotient.Respect

World "Quotient"
Level 4

Title "Quotient"

Introduction
"
In this level you prove that the quotient lift of `rangeFactorization f` with respect to the
congruence relation `ker f` is a bijection.

Given a map `f : A → B`, the theorem `ker_lift_injective` says that the canonical map from the quotient of `A` by the congruence `ker f` to `B` is injective.

"

open Function Set Setoid Quotient

#check rangeFactorization_eq

#check ker_lift_injective

section
variable {α : Type*} {β : Type*} (f : α → β)

#check Quotient.mk
#check Quotient.mk'

#check @Quotient.lift _ _ (ker f) f (fun _ _ h => h)

#check ker_lift_injective (rangeFactorization f)


theorem ker_lift_injective (f : α → β) : Injective (@Quotient.lift _ _ (ker f) f fun _ _ h => h) :=
  fun x y => Quotient.inductionOn₂' x y fun _ _ h => Quotient.sound' h

end

Statement bij_quotient_lift_range_fac (f : A → B) :
    Bijective (Quotient.lift (rangeFactorization f) respects_ker_rel) := by
  constructor
  · intro x y h
    sorry
  · sorry
