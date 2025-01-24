import Game.Metadata
import Game.Levels.SetTheory.L12_Insert


World "SetTheory"
Level 13

Title "Konkrete Mengen"

Introduction
"
**Verkäufer**: Ja, also hier ein besseres Beispiel:

Um zu überprüfen, dass gewisse Elemente in
konkreten Mengen enthalten sind, gibt es nicht direkt eine Taktik, aber ein
einfaches Rezept:

```
simp_rw [mem_insert_iff, mem_singleton_iff] at *
```

vereinfacht Aussagen der Form `6 ∈ {0, 6, 1}` zu `(6 = 0) ∨ (6 = 6) ∨ (6 = 1)`,
und dann kann `tauto` diese Aussage beweisen.

Bei `⊆` kann man wie schon vorher zuerst mit `intro x hx` die Definition
auseinandernehmen und dann gleich vorgehen.

"

open Set

Statement :
    ({2, 3, 5} : Set ℕ) ⊆ {4, 2, 5, 7, 3} := by
  Hint "Fang wieder mit `rw [subset_def]` oder direkt mit `intro` an."
  intro x hx
  Hint "**Du**: Das ist ja die eigentliche Aufgabe.

  **Verkäufer**: Solche Aufgaben sind immer mit
    `simp_rw [mem_insert_iff, mem_singleton_iff] at *` gefolgt von `tauto` lösbar!"
  simp_rw [mem_insert_iff, mem_singleton_iff] at *
  Hint "**Robo**: Das kann aber ganz schön lang werden.

  **Verkäufer**: Ich habe mir noch nie überlegt, was passiert wenn man über zu große Mengen
  nachdenkt…"
  tauto

Conclusion "Damit lässt ihr den Verkäufer mit seinen Mengen an Obst zurück und wandert weiter."

NewTheorem Set.mem_insert_iff Set.mem_singleton_iff
TheoremTab "Set"
