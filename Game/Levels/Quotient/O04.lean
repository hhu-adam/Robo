import Game.Metadata

World "Quotient"
Level 4

Statement Quotient.surjective_lift {A B : Type*} (s : Setoid A) {f : A → B}
    (f_resp_rel : ∀ a₁ a₂, a₁ ≈ a₂ → f a₁ = f a₂) :
    Function.Surjective (Quotient.lift f f_resp_rel) ↔ Function.Surjective f := by
  constructor
  · intro h y
    obtain ⟨q, hq⟩ := h y
    induction q using Quotient.ind
    use a
    apply hq
  · intro h y
    obtain ⟨a, ha⟩ := h y
    use ⟦a⟧
    apply ha
