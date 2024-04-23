import Game.Metadata
import Game.Levels.SetTheory.L06_Nonempty

World "SetTheory"
Level 7

Title "Schnittmenge und Vereinigung"

Introduction
"
Eine alte Dame kommt daher und wendet sich zu Verkäufer.

**Dame**: Du, ich hatte einen Gedanken. Kannst du mir folgendes erklären?
"

open Set

Statement (A B : Set ℕ) : (A ∪ ∅) ∩ B = A ∩ (univ ∩ B) := by
  simp

TheoremTab "Set"
