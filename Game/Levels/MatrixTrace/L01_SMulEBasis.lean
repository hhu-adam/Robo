import Game.Metadata
import Game.Levels.Sum

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

World "Trace"
Level 1

Title "E-Basis"

-- TODO: Do we need this level??

Introduction
"
The matrix `E i j` is defined as the matrix with a `1` at position `i, j` and `0` elsewhere. They are extemely sparse. In below, `E i j` are defined in terms of mathlib's `stdBasisMatrix`.

`stdBasisMatrix i j c` is the matrix with `c` at position `i, j` and `0` elsewhere. `stdBasisMatrix` matrices are closed under scalar multiplication, becasue
`c • stdBasisMatrix i j 1 = stdBasisMatrix i j c`, a theorem witnessed by `smul_stdBasisMatrix`.

"

open Nat Matrix BigOperators

/-- `E i j` ist die `n × n`-Matrix (mit Werten in `ℝ`) mit einer `1` an
Stelle `(i, j)` und null überall sonst.

Bemerkung: Dies ist eine spezialisierte Form der generellen `stdBasisMatrix i j (a : R)`,
welche auch nicht-quadratisch sein kann und einen beliebigen Wert `a` aus einem beliebigen
Ring annehmen kann.

Das Spiel bevorzugt `E` um die lesbarkeit zu erhöhen.
-/
def Matrix.E {n : ℕ} (i j : Fin n) : Mat[n,n][ℝ] :=
  stdBasisMatrix i j 1

/-- `E i j` ist die `n × n`-Matrix (mit Werten in `ℝ`) mit einer `1` an
Stelle `(i, j)` und null überall sonst.

Bemerkung: Dies ist eine spezialisierte Form der generellen `stdBasisMatrix i j (a : R)`,
welche auch nicht-quadratisch sein kann und einen beliebigen Wert `a` aus einem beliebigen
Ring annehmen kann.

Das Spiel bevorzugt `E` um die lesbarkeit zu erhöhen.
-/
DefinitionDoc Matrix.E as "E"



Statement Matrix.smul_ebasis {n : ℕ} (A : Mat[n,n][ℝ]) (i j) :
    A i j • E i j = stdBasisMatrix i j (A i j) := by
  unfold E
  simp



NewDefinition Matrix.E
TheoremTab "Matrix"
