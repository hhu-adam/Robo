import Game.Metadata


World "Function"
Level 6

Title "Verzweigung"

Introduction "
Für eine nicht-negative ganze Zahl `(n : ℤ)` ist `n.toNat` die entsprechende
Zahl als Element von `ℕ` betrachtet.
"

open Function Set Nat

Statement {A : Type} [h : Nonempty A] (f : ℕ → A) :
    ∃ g : ℤ → A, ∀ n : ℕ, (f n = g n) := by
  Hint "**Robo**: Ich vermute, du solltest als erstes mal ein Element aus `A` wählen …"
  Hint (hidden := true) "**Robo**: … zum Beispiel mit `obtain ⟨a₀⟩ := h`."
  obtain ⟨a₀⟩ := h
  Hint "**Robo**: Und jetzt versuch mal, die richtige Funktion zu definieren: `let g : ℤ → {A} :=` usw."
  Hint (hidden := true) "**Robo**: Du könntest eine stückweise Funktion mit `if 0 ≤ n then ... else ...`
  definieren."
  let g : ℤ → A := fun n ↦ if (0 ≤ n) then f n.toNat else a₀
  Hint (strict := true) "**Robo**: Jetzt kannst du dein definiertes `g` mit `use` brauchen, und
  sehen, ob deine Definition gut war."
  use g
  intro n
  simp [g] -- TODO: There's a tiny bit magic in this step.


NewTactic  «if»
NewHiddenTactic «then»  «else»
