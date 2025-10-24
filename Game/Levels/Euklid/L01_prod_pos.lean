import Game.Metadata

World "Euklid"
Level 1
Title ""

/- Introduction "An der markierten Stelle steht folgendes:" -/
Introduction "`INTRO` Intro Euklid L01"

open Finset
namespace Nat

Statement (A : Finset ℕ) (h : ∀ a ∈ A, Prime a) : 0 < (∏ a ∈ A, a) := by
  /-
  Hint "**Du**:  Die Zeile ist tatsächlich lesbar.
  `∏ a ∈ A, a` ist sicher Leansch für das Produkt über alle Zahlen aus `A`, oder?

  **Robo**:  Ja!  Und die nächste Zeile ergibt auch Sinn: `apply prod_pos`."
  -/
  Hint "Try `apply prod_pos`"
  apply prod_pos
  /-
  Hint "**Robo**: Aber was danach kommt, ist wieder völliger Unsinn.
  Die Aussage selbst stimmt aber, denke ich. Komm, das schaffen wir selbst."
  -/
  Hint "Story"
  intro a ha
  specialize h a ha
  rw [prime_def] at h
  linarith

/---/
TheoremDoc Finset.prod_pos as "prod_pos" in "∑ Π"

NewTheorem Finset.prod_pos

NewDefinition Prod
