-- imports used in custom tactics
import Mathlib.Lean.Expr.Basic
import Mathlib.Tactic.Cases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring


import Mathlib.Tactic
import Mathlib.Data.Nat.Parity
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.LinearIndependent
import Mathlib.Data.Real.Basic           -- definiert `ℝ`
import Mathlib.LinearAlgebra.Basis
import Mathlib.Data.Real.Basic            -- definiert `ℝ`
import Mathlib.Algebra.Module.Pi          -- definiert `Module ℚ (fin 2 → ℚ)`
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

import Mathlib.Init.Data.Nat.Basic -- Imports the notation ℕ.
-- import Std.Tactic.RCases

-- not imported by default but important for the game.
-- enables `have x : A` as a tactic.
import Mathlib.Tactic.Have

-- TODO
import Mathlib
