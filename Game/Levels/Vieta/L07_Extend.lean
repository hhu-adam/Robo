import Game.Metadata


World "Vieta"
Level 7

Title "" -- "Verzweigung"

/-
Introduction "
Ihr hört aus der Ferne Kampfgeräusche.  Vieta scheint nach wie vor nicht beunruhigt.
Er gibt euch noch eine Aufgabe.
"
-/
Introduction "`INTRO` Intro Vieta L07"

open Function Set Nat

Statement {A : Type} (f : ℕ → A) :
    ∃ g : ℤ → A, ∀ n : ℕ, (f n = g n) := by
  /-
  Hint "
    **Robo**:  Hier brauchst du wahrscheinlich `toNat`:  ist `n : ℤ` eine ganze Zahl,
       ist `n.toNat : ℕ` dieselbe Zahl, aber aufgefasst als natürliche Zahl.

    **Du**:  Wie?  Was ist denn dann z.B. `(-1).toNat`??

    **Robo**:  Keine Ahnung.  Was ich meinte, ist natürlich:  *falls `n ≥ 0` ist*,
               dann ist `n.toNat` immer noch „dieselbe“ Zahl.
    "
  -/
  Hint "Try `toNat`. Explain, given `n : ℤ` then `n.toNat : ℕ` is the same number interpreted as a natural number.
  Remind that `(-1).toNat` undefined as `n ≥ 0` for `n.toNat`"
  -- Hint (hidden := true) "**Robo**: Du könntest eine stückweise Funktion mit `if 0 ≤ n then … else …`
  -- definieren."
  Hint (hidden := true) "Try function with `if 0 ≤ n then … else …`"
  let g : ℤ → A := fun n ↦ if (0 ≤ n) then f n.toNat else f 0
  /-
  Hint (strict := true) "**Robo**: Jetzt kannst du dein `g` mit `use` einsetzen und
  sehen, ob deine Definition gut war."
  -/
  Hint (strict := true) "Insert `g` via `use`"
  use g
  intro n
  simp [g] -- TODO: There's a tiny bit magic in this step.


NewDefinition toNat
