import Game.Metadata
import Game.Levels.Cantor.L06_idempotent

World "Cantor"
Level 7

Title "Cantor"

Introduction
"
"

open Function Set

-- Now moved back as hint inside Lvl 8, so not needed anymore
Statement cantor_diagonal_isFixedPt {f : A → A → Y} {c : A → Y} {s : Y → Y}
    (c_apply : ∀ b, c b = s (f b b)) (a : A) (c_surj : c = f a) :
    IsFixedPt s (f a a) := by
  unfold IsFixedPt
  rw [← c_apply]
  rw [c_surj]
