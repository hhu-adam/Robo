import Batteries
import GameServer
import Game.Doc

-- must be imported *before* the custom modifications!
import Game.Metadata.Tactic
import Game.Metadata.FromMathlib

import Game.Metadata.MatrixNotation

-- mathlib PR: 85107
theorem Set.subset_iff {A : Type} {s₁ s₂ : Set A} : s₁ ⊆ s₂ ↔ ∀ {x : A}, x ∈ s₁ → x ∈ s₂ := by
  rfl

-- import Game.Metadata.Delaborator
-- import Game.Metadata.DelaboratorFunOnProd
-- import Game.Metadata.SetBuilder    -- Marcus: This file is just comment!? So I removed it.

#min_imports
