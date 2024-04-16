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

-- RP'd to mathlib: #85107
/-- Short notation for `n x m`-Matrices. -/
notation (name := concreteMatrix) "Mat["n","m"]["R"]" => Matrix (Fin n) (Fin m) R
