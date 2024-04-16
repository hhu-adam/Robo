import Game.Metadata
import Game.Levels.Sum

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

World "Trace"
Level 1

Title "E-Basis"

Introduction
"
Den Spuren folgend, findet ihr ein Stück Pergament, auf dem zuoberst
eine Notiz steht.

```
E i j := stdBasisMatrix i j (1 : ℝ)
```

Darunter ein bisschen wildes Gekritzel, was aber deutlich mit einer klaren
Zeile angefangen hat:
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
  stdBasisMatrix i j (1 : ℝ)

/-- `E i j` ist die `n × n`-Matrix (mit Werten in `ℝ`) mit einer `1` an
Stelle $(i, j)$ und null überall sonst.

Bemerkung: Dies ist eine spezialisierte Form der generellen `stdBasisMatrix i j (a : R)`,
welche auch nicht-quadratisch sein kann und einen beliebigen Wert `a` aus einem beliebigen
Ring annehmen kann.

Das Spiel bevorzugt `E` um die lesbarkeit zu erhöhen.
-/
DefinitionDoc Matrix.E as "E"

Statement Matrix.smul_ebasis {n : ℕ} (A : Mat[n,n][ℝ]) (i j) :
    A i j • E i j = stdBasisMatrix i j (A i j) := by
  Hint "**Du**: Bei dem Wesen gings wohl um Matrizen. Was es wohl sein mag?

  **Robo**: `stdBasisMatrix i j (1 : ℝ)` kenne ich, das ist die Standardbasis
  von Matrizen, die genau 1 sind an Position `(i, j)` und sonst überall Null.

  **Du**: Und die `E`s sind dann einfach eine Abkürzung?

  **Robo**: Genau, die hat es sich wohl aufgeschrieben, da es nur mit quadratischen
  $n \\times n$-Matrizen auf $\\mathbb\{R}$ arbeitet.

  **Du**: Dann ist das ja fast nur die Definition?

  **Robo**: Ja. Ich denke wenn du mit `unfold E` anfängst, ist der Rest einfach
  nur vereinfachen.
  "
  unfold E
  simp

Conclusion "**Du**: Ob das wohl was bringt?

**Robo**: Ich speichere das mal als `Matrix.smul_ebasis` ab, falls wir es nochmals
brauchen.

Damit folgt ihr der Spur weiter.
"

NewDefinition Matrix.E
TheoremTab "Matrix"
