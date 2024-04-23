import Game.Metadata
import Game.Levels.SetTheory.L07_UnionInter

World "SetTheory"
Level 8

Title "Schnittmenge und Vereinigung"

Introduction
"
**Verkäufer**: Ich habe aber was interessanteres:
"

open Set

/--  -/
Statement (A B : Set ℕ) : univ \ (A ∩ B) = (univ \ A) ∪ (univ \ B) ∪ (A \ B) := by
  Hint "**Robo**: Ich habe dir ein paar Sachen aus meinem Speicher zusammengekratzt."
  rw [diff_inter]
  Hint (hidden := true) "mit `union_assoc` und `union_diff_distrib` kannst du
  auf der rechten Seite weiterkommen."
  rw [union_assoc]
  rw [←union_diff_distrib]
  rw [univ_union]

DisabledTactic tauto
NewTheorem Set.diff_inter Set.union_assoc Set.union_diff_distrib Set.univ_union
TheoremTab "Set"

-- Nein kann es nicht. Wieso nicht?
-- Conclusion "Wie du vielleicht bemerkt hast, könnte `tauto` sowas automatisch lösen."
