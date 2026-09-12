import Game.Metadata
import Mathlib.CategoryTheory.ConcreteCategory.Bundled

open CategoryTheory

noncomputable section

def FiniteSets : Type 2 :=
    { A : Type 1 // Finite A}

namespace FiniteSets

/-- Treat an element of `FiniteSets` as the type it bundles. -/
instance : CoeSort FiniteSets (Type 1) := ⟨Subtype.val⟩

instance (A : FiniteSets) : Finite A := A.2

/-- Bundle a finite type (in `Type 1`) as an element of `FiniteSets`. -/
def of (α : Type 1) [Finite α] : FiniteSets := ⟨α, ‹_›⟩

/-- Two elements of `FiniteSets` are equivalent when there is a bijection between them. -/
instance setoid : Setoid FiniteSets where
  r A B := Nonempty (A ≃ B)
  iseqv :=
    { refl _ := ⟨Equiv.refl _⟩
      symm := fun ⟨e⟩ => ⟨e.symm⟩
      trans := fun ⟨e₁⟩ ⟨e₂⟩ => ⟨e₁.trans e₂⟩ }

/-- The quotient of all finite sets by "there is a bijection" is `ℕ`,
the equivalence being given by the number of elements. -/
def quotientEquivNat : Quotient setoid ≃ ℕ := by
  apply Equiv.ofBijective
    (Quotient.lift (fun A : FiniteSets => Nat.card A)
      (fun _ _ h => Finite.card_eq.mpr h))
  constructor
  · intro x y h
    induction x using Quotient.ind
    induction y using Quotient.ind
    apply Quotient.sound
    apply Finite.card_eq.mp h
  · intro n
    use ⟦of (ULift.{1} (Fin n))⟧
    show Nat.card (ULift.{1} (Fin n)) = n
    rw [Nat.card_ulift, Nat.card_fin]

end FiniteSets

/-- A "finite set": a type bundled with a `Fintype` instance on it. -/
abbrev FinType := Bundled Fintype

instance (A : FinType) : Fintype A := A.str

/-- Bundle a type with its `Fintype` instance. -/
abbrev FinType.of (α : Type) [Fintype α] : FinType := Bundled.of α

/-- `Fin n` is a `Type`, not a `FinType`; `FinType.of` turns it into one by
picking up the instance `Fintype (Fin n)`. -/
example (n : ℕ) : FinType := FinType.of (Fin n)

/-- Two finite types are equivalent when there is a bijection between them. -/
instance finTypeSetoid : Setoid FinType where
  r A B := Nonempty (A ≃ B)
  iseqv :=
    { refl _ := ⟨Equiv.refl _⟩
      symm := fun ⟨e⟩ => ⟨e.symm⟩
      trans := fun ⟨e₁⟩ ⟨e₂⟩ => ⟨e₁.trans e₂⟩ }

/-- The quotient of all finite types by "there is a bijection" is `ℕ`. -/
def finTypeQuotientEquivNat : Quotient finTypeSetoid ≃ ℕ := by
  apply Equiv.ofBijective
    (Quotient.lift (fun A : FinType => Fintype.card A)
      (fun _ _ h => Fintype.card_eq.mpr h))
  constructor
  · intro x y h
    induction x using Quotient.ind
    induction y using Quotient.ind
    apply Quotient.sound
    apply Fintype.card_eq.mp h
  · intro n
    use ⟦FinType.of (Fin n)⟧
    apply Fintype.card_fin n
