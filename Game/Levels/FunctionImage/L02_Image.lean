import Game.Metadata

open Function Set

World "FunctionImage"
Level 2
Title "Bild/Urbild"

Introduction "
unangewendetes image/preimage als Funktion
"

-- Turn into level 2, explain `image`/`preimage`
Statement {A B C : Type} (f : A → B) (g : B → C) : image (g ∘ f) = (image g) ∘ (image f) := by
  funext S
  ext c
  simp
