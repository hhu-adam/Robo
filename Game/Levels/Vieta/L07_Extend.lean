import Game.Metadata


World "Vieta"
Level 7

Title "" -- "Verzweigung"

Introduction "
Ihr hört aus der Ferne Kampfgeräusche.  Vieta scheint nach wie vor nicht beunruhigt.
Er gibt euch noch eine Aufgabe.
"

open Function Set Nat

Statement {A : Type} (f : ℕ → A) :
    ∃ g : ℤ → A, ∀ n : ℕ, (f n = g n) := by
  Hint "
    **Robo**:  Hier brauchst du wahrscheinlich `toNat`:  ist `n : ℤ` eine ganze Zahl,
       ist `n.toNat : ℕ` dieselbe Zahl, aber aufgefasst als natürliche Zahl.

    **Du**:  Wie?  Was ist denn dann z.B. `(-1).toNat`??

    **Robo**:  Keine Ahnung.  Was ich meinte, ist natürlich:  *falls `n ≥ 0` ist*,
               dann ist `n.toNat` immer noch „dieselbe“ Zahl.
    "
  Hint (hidden := true) "**Robo**: Du könntest eine stückweise Funktion mit `if 0 ≤ n then ... else ...`
  definieren."
  let g : ℤ → A := fun n ↦ if (0 ≤ n) then f n.toNat else f 0
  Hint (strict := true) "**Robo**: Jetzt kannst du dein `g` mit `use` einsetzen und
  sehen, ob deine Definition gut war."
  use g
  intro n
  simp [g] -- TODO: There's a tiny bit magic in this step.


NewDefinition toNat


NewTactic  «if»
NewHiddenTactic «then»  «else»
