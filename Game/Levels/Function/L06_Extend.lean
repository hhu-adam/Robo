import Game.Metadata


World "Function"
Level 6

Title "Choosing an arbitrary element of a nonempty type."


Introduction
"
Wenn du ein beliebiges Element aus `A` brauchst, kannst du
`Classical.arbitrary A` nehmen.

Zudem, für eine nicht-negative Ganzzahl `(n : ℤ)` ist `n.toNat` die entsprechende
Zahl als Element von `ℕ` betrachtet.
"

open Function Set Nat

Statement {A : Type} [h : Nonempty A] (f : ℕ → A) :
    ∃ g : ℤ → A, ∀ n : ℕ, (f n = g n) := by
  Hint " Versuch erst mal, die richtige Funktion zu definieren: `let g : ℤ → {A} :=` usw."
  Hint (hidden := true) "Du könntest eine stückweise Funktion mit `if 0 ≤ x then ... else ...`
  definieren."
  let g : ℤ → A := fun n ↦ if (0 ≤ n) then f n.toNat else Classical.arbitrary A
  Hint (strict := true) "Jetzt kannst du dein definiertes `g` mit `use` brauchen, und
  sehen, ob deine Definition gut war."
  use g
  intro n
  simp [g] -- TODO: There's a tiny bit magic in this step.

NewTheorem Classical.arbitrary
