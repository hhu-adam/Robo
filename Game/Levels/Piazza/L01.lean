
import Game.Metadata

World "Piazza"
Level 1

Title "" -- "Mengen"

Introduction
"
Eine beliebige Menge von natürlichen Zahlen ist `A : Set ℕ`, oder wenn man diese
explizit definiert `{1, 6, 4} : Set ℕ`

In diesem Planeten wollen wir die meisten Aussagen aus der Mengenlehre auf Logik
reduzieren, damit wir sie mit `tauto` lösen können.
"

open Set

Statement : 1 ∈ ({1, 6, 4} : Set ℕ) := by

  Hint "Diese Aussage läst sich intern auf
  `1 = 1 ∨ 1 = 6 ∨ 1 = 4` reduzieren, deshalb kann `tauto` direkt beweisen,
  dass etwas in einer konkreten Menge liegt."
  tauto

/-- -/
DefinitionDoc Mem as "∈"

/-- -/
DefinitionDoc Set as "Set"

NewDefinition Mem Set
TheoremTab "Set"

Conclusion ""
