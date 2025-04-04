/- imports used in custom tactics -/
import Mathlib.Lean.Expr.Basic
-- import Mathlib.Tactic.Cases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
/- other tactics                 -/
import Mathlib.Tactic -- removing this seems difficult, I get lots of errors that are not obviously related to missing tactics
--import Mathlib.Tactic.ByContra
--import Mathlib.Tactic.Choose
--import Mathlib.Tactic.Constructor
--import Mathlib.Tactic.Contrapose
--import Mathlib.Tactic.Generalize
--import Mathlib.Tactic.Have
--import Mathlib.Tactic.Simps.Basic
--import Mathlib.Tactic.Simps.NotationClass

/- other parts of mathlib         -/
import Mathlib.Init.Data.Nat.Basic -- Imports the notation ℕ.
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Nat.Prime
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic           -- definiert `ℝ`
import Mathlib.LinearAlgebra.Basis
import Mathlib.Data.Real.Basic            -- definiert `ℝ`
import Mathlib.Algebra.Module.Pi          -- definiert `Module ℚ (fin 2 → ℚ)`
--import Mathlib.Data.Fin.VecNotation
--import Mathlib.LinearAlgebra.LinearIndependent
