import Game.Metadata

World "Symmetric Square"
Level 10

Introduction "Intro Symm L10"

open Function Sym Sym2

attribute [local instance] Sym2.Rel.setoid

variable {A B : Type*}

Statement Sym_g : {f : A → A → B | ∀ a b, f a b = f b a} → (Sym2 A → B) := by
  Hint "[Hint s10lift] `Quotient.lift` is the machine that turns a function on `A × A` into one
    on the quotient — provided the function respects `≈`. The previous level is precisely that
    proof, so here you feed both to `Quotient.lift`."
  Hint "[Hint s10sub] The argument lives in a *subtype*: it carries a function
    together with the proof that this function is symmetric. `intro ⟨f, hf⟩` takes both apart
    at once."
  intro ⟨f, hf⟩
  Hint "[Hint s10qlf] `Quotient.lift` lifts a function from an underlying type to a function on a
    quotient, requiring that it respects the quotient's equivalence relation."
  Hint (hidden := true) "[Hint s10unc] Combine `Quotient.lift` and `uncurry`. Remember that
    `uncurry` transforms a function of type `α → β → φ` into an equivalent function of type
    `α × β → φ`."
  apply Quotient.lift (uncurry f)
  Hint "[Hint s10resp] Now it remains to prove that `uncurry {f}` respects the quotient's
    equivalence relation."
  intro a b hab
  cases hab
  · rfl
  · apply hf

NewDefinition Quotient.lift Function.uncurry
