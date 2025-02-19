import Game.Metadata

World "SetTheory"
Level 8

Title "" -- "Übung"

Introduction
"
So, jetzt sind wir richtig beim Üben angekommen.

Ah und `A \\ B` ist die Differenz von Mengen, das ist aber nicht
so wichtig für das Lösen der Aufgabe.
"

open Set

Statement (A B : Set ℕ) :
    univ \ (A ∩ B) = (univ \ A) ∪ (univ \ B) ∪ (A \ B) := by
  Hint (hidden := true) "Als erster Schritt, die Mengengleichung, wird mit `ext` angegangen."
  ext i
  Hint (hidden := true) "Als zweiter Schritt, sobald man `∈ _` hat, macht `simp` weiter."
  simp
  Hint (hidden := true) "Als letzter Schritt, für eine Logik-Aussage,
  wird mit `tauto` geschlossen."
  tauto


/-- -/
DefinitionDoc SDiff as "·\\·"

NewDefinition SDiff
TheoremTab "Set"

Conclusion ""
