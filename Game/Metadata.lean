import Batteries
import GameServer
import Game.Doc

-- must be imported *before* the custom modifications!
import Game.Metadata.FromMathlib

import Game.Metadata.Tactic
import Game.Metadata.Tactic.simp_list
import Game.Metadata.MatrixNotation
import Game.Metadata.DelaboratorNatSucc


/-- subset.def versus subset_iff --/
/- mathlib has three lemmas of this kind
  
  #check Set.subset_def      -- (a)
  #check Finset.subset_def   -- (b)
  #check Finset.subset_iff   -- (c)

  Unfortunately, (a) is more similar to (b) than to (c).
  mathlib PR #35416 tried to resolve this but faild.

  Current workaround:
-/
alias Set.subset_iff := Set.subset_def


-- import Game.Metadata.Delaborator
-- import Game.Metadata.DelaboratorFunOnProd
-- import Game.Metadata.SetBuilder    -- Marcus: This file is just comment!? So I removed it.

#min_imports
