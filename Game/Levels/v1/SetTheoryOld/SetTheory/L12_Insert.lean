import Game.Metadata
import Game.Levels.SetTheory.L11_SSubset


World "SetTheory"
Level 12

Title "Konkrete Mengen"

Introduction
"
**Du**: Das ist ja alles schön und gut, aber ich weiß immer noch nicht, wie
ich eine ganz simple Menge wie `{4, 9}` notiere…

**Verkäufer**: Genau so! Aber diese endlichen Mengen sind alles iterative
Konstruktionen aus `Set.insert` und `singleton`. Hier zum Beispiel:
"

open Set

/-- Die Menge `{4, 9}` ist per Definition `{4} ∪ {9}`. -/
Statement :
    ({4, 9} : Set ℕ) = Set.insert 4 {9} := by
  Hint "**Du**: Das wär ja dann `rfl`."
  rfl

OnlyTactic rfl
TheoremTab "Set"
