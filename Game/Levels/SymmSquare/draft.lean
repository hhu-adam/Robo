import Game.Metadata

open Finset

/-- Two finsets are equivalent when they have the same cardinality. -/
def cardSetoid (α : Type*) : Setoid (Finset α) where
  r s t := s.card = t.card
  iseqv :=
    { refl _ := rfl
      symm h := h.symm
      trans h₁ h₂ := h₁.trans h₂ }

/-- Two finsets of reals are equivalent when there exists an equiv (a bijection)
between them, viewed as types via their coercions. -/
def isoSetoid : Setoid (Finset ℝ) where
  r s t := Nonempty (s ≃ t)
  iseqv :=
    { refl _ := ⟨Equiv.refl _⟩
      symm := fun ⟨e⟩ => ⟨e.symm⟩
      trans := fun ⟨e₁⟩ ⟨e₂⟩ => ⟨e₁.trans e₂⟩ }

/-- For finsets, "there is a bijection between them" is the same as "they have
the same cardinality": `isoSetoid` and `cardSetoid` are the same relation on
`Finset ℝ`. -/
theorem isoSetoid_iff_card (s t : Finset ℝ) :
    isoSetoid.r s t ↔ (cardSetoid ℝ).r s t := by
  suffices h : Nonempty (s ≃ t) ↔ s.card = t.card
  · apply h
  rw [← Fintype.card_eq, Fintype.card_coe, Fintype.card_coe]

/-- When `α` is infinite, the quotient of `Finset α` by "same cardinality" is
equivalent (as a type) to `ℕ`: the cardinality map descends to the quotient,
is injective by construction, and is surjective because an infinite type has
finsets of every cardinality (`Infinite.exists_subset_card_eq`). -/
noncomputable def cardQuotientEquivNat (α : Type*) [Infinite α] :
    Quotient (cardSetoid α) ≃ ℕ :=
  Equiv.ofBijective (Quotient.lift Finset.card (fun _ _ h => h)) <| by
    constructor
    · -- injective
      intro x y h
      induction x using Quotient.ind
      induction y using Quotient.ind
      exact Quotient.sound h
    · -- surjective
      intro n
      obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq α n
      exact ⟨⟦s⟧, hs⟩
