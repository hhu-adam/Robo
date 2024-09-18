import Game.Metadata


World "Function"
Level 5

Title "Choosing an arbitrary element of a nonempty type."


Introduction
"
"

open Function Set Nat


Statement {A : Type} [h : Nonempty A] (f : ℕ → A) :
    ∃ g : ℤ → A, ∀ n : ℕ, (f n = g n) := by
  Hint "`Classical.arbitrary {A}` ist ein beliebiges Element in `{A}`,
  `n.toNat` ist entweder die Ganzahl als natürliche Zahl gesehen oder `0` für negative Ganzzahlen.

  Versuch erst mal, die richtige Funktion zu definieren: `let g : ℤ → {A} :=` usw."

  let g : ℤ → A := fun n ↦ if (0 ≤ n) then f n.toNat else Classical.arbitrary A
  use g
  intro n
  simp [g]

NewTheorem Classical.arbitrary
