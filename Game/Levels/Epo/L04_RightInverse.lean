import Game.Metadata


World "Epo"
Level 4

Title ""

Introduction ""

open Function

-- in mathlib: `Function.rightInverse_iff_comp`
Statement {A B : Type} {f : A -> B} {g : B -> A} :
    RightInverse g f ↔ f ∘ g = id := by
  Hint "
  **Du**:  Jetzt muss ich mich wohl doch ein bisschen durch die Definitionen hangeln?

  **Robo**: Sieht so aus."
  Hint (hidden := true) "
  **Robo:**:  Ich würde tatsächlich wieder mit `constructor` anfangen.
  Und dann die üblichen Verdächtigen wie `comp_apply`, `congr_fun` usw. nutzen."
  constructor
  · intro h
    funext x
    Branch
      rw [comp_apply]
      rw [h x]
      rw [id_eq]
    apply h
  · Branch
      apply congr_fun
      done
    intro h
    intro x
    Hint (hidden := true) "
    **Robo**:  Du könntest mit `apply congr_fun at h` oder `rw [← comp_apply (f:= f)]`.
    (`rw [← comp_apply]` ohne `(f:=f)` funktioniert hier nicht
    – du musst explizit angeben, welchen Wert die Variable `f` in der Aussage von `comp_apply` haben soll."
    Branch
      rw [← comp_apply (f:= f)]
      rw [h]
      rfl
    apply congr_fun at h
    apply h

TheoremTab "Function"
