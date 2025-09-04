--import Mathlib    -- Marcus: This needs to go.
import Batteries
import GameServer
import Game.Doc

-- must be imported *before* the custom modifications!
-- import Game.Metadata.FromMathlib

-- import Game.Metadata.Coersion

import Game.Metadata.Tactic

--import Game.Metadata.MathlibPreview  -- Marcus: This needs to go.
-- MathlibPreview still imports Mathlib, and should be superfluous for the most part.
-- Temporarily including a few lines here:

-- mathlib PR: 85107
theorem Set.subset_iff {A : Type} {s₁ s₂ : Set A} : s₁ ⊆ s₂ ↔ ∀ {x : A}, x ∈ s₁ → x ∈ s₂ := by
  rfl





-- import Game.Metadata.Delaborator
-- import Game.Metadata.DelaboratorFunOnProd
--import Game.Metadata.SetBuilder    -- Marcus: This file is just comment!? So I removed it.

-- import Game.Metadata.MatrixNotation
-- MatrixNotation still imports Mathlib, and I don't know how to fix it.
-- For now, just include one essential line from that file here:
namespace Matrix
notation (name := concreteMatrix) "Mat["n","m"]["R"]" => Matrix (Fin n) (Fin m) R
end Matrix
