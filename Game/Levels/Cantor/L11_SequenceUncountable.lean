import Game.Metadata
import Game.Levels.Cantor.L10_CantorPowerset

World "Cantor"
Level 11

Title ""

Introduction "
  **Cantor**:  Einfacher?  Weiß nicht.  Aber eleganter!

  Er macht drei Saltos rückwarts und kommt
  dann mit einem weiteren Zettel für euch zurück.

  **Cantor**:  Schaut mal!  Jetzt könnt ihr mit demselben Argument zeigen,
  dass die Menge der Folgen natürlicher Zahlen, also die Menge der Abbildungen `ℕ → ℕ`,
  überabzählbar ist!

  Und dann im Flüsterton:

  **Cantor**:  Es gibt in diesem Zelt überabzählbar viele Plätze!
"

Conclusion "
  **Robo**:  Vielen Dank für die Vorstellung!

  **Du**:  Aber schade, dass es so wenige Zuschauer gibt!

  **Cantor**:  Zauberei ist eben nicht für jedermann.  Gute Weiterreise!
"

open Nat Set Function

Statement : ¬ ∃ f : ℕ → ℕ → ℕ, Surjective f := by
  push_neg
  intro f
  by_contra hf
  apply cantor_diagonal at hf
  Hint (hidden := true) "
    **Du**:  Wie hieß noch einmal die Abbildung `n ↦ n + 1`?

    **Robo**: `succ`
  "
  specialize hf succ
  obtain ⟨n, hn⟩ := hf
  unfold fixedPoints IsFixedPt at hn
  simp at hn -- dsimp [IsFixedPt] at hn
  --simp only [Nat.succ_ne_self] at hn


TheoremTab "Function"
