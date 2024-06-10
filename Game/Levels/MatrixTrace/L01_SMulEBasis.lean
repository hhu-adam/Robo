import Game.Metadata
import Game.Levels.Sum

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

World "Trace"
Level 1

Title "Standardbasis"

Introduction
"
Den Spuren folgend, findet ihr ein Stück Pergament, auf dem zuoberst
eine Notiz steht.

```
E i j := stdBasisMatrix i j (1 : ℝ)
```

Darunter ein bisschen wildes Gekritzel, das aber deutlich mit einer klaren
Zeile angefangen hat:
"

open Nat Matrix BigOperators

def Matrix.E {n : ℕ} (i j : Fin n) : Mat[n,n][ℝ] :=
  stdBasisMatrix i j (1 : ℝ)

/-- `E i j` ist die `n × n`-Matrix (mit Werten in `ℝ`) mit einer `1` an
Stelle $(i, j)$ und null überall sonst.

Bemerkung: Dies ist eine spezialisierte Form der generellen `stdBasisMatrix i j (a : R)`,
welche auch nicht-quadratisch sein kann und einen beliebigen Wert `a` aus einem beliebigen
Ring annehmen kann.

Das Spiel bevorzugt `E`, um die Lesbarkeit zu erhöhen.
-/
DefinitionDoc Matrix.E as "E"

/---/
TheoremDoc Matrix.smul_ebasis as "smul_ebasis" in "Matrix"

Statement Matrix.smul_ebasis {n : ℕ} (A : Mat[n,n][ℝ]) (i j) :
    A i j • E i j = stdBasisMatrix i j (A i j) := by
  Hint "**Du**: Welches Wesen auch immer hier Spuren hinterlassen hat – mir scheint, es mag Matrizen. Was meints du?

  **Robo**: Ja! `stdBasisMatrix i j a` kenne ich, das ist die Matrix, die an der Position `(i, j)` den Eintrag `a` hat und sonst überall Null ist.

  **Du**: Und die `E`s sind dann einfach eine Abkürzung für den Fall `a = 1`?

  **Robo**: So sieht's aus. Und `A i j` ist einfach der Eintrag der Matrix `A` an der Position `(i, j)`.

  **Du**: Ah, verstehe. Da steht also kein Produkt von Matrizen, sondern nur eine Skalarmultiplikation. Etwas in der Art von …

  Du kritzelst auf das Papier:

  $$
  A_\{i,j} \\cdot 
  \\begin\{pmatrix}
  0 & 0 & 0\\\\
  1 & 0 & 0 \\\\
  0 & 0 & 0 
  \\end\{pmatrix}
  =
  \\begin\{pmatrix}
  0 & 0 & 0\\\\
  A_\{i,j} & 0 & 0 \\\\
  0 & 0 & 0 
  \\end\{pmatrix}
  $$

  **Du**: Dann ist das ja mal wieder… …offensichtlich!?

  **Robo**: Ja. Ich denke, wenn du mit `unfold E` anfängst, geht der Rest wie von selbst.
  "
  unfold E
  simp

Conclusion "**Du**: Und was machen wir jetzt mit dieser „Erkenntnis“?

**Robo**: Keine Ahnung.  Ich speichere das jedenfalls mal als `Matrix.smul_ebasis` ab, falls wir es nochmals
brauchen.

Damit folgt ihr weiter der Spur.
"

NewDefinition Matrix.E
TheoremTab "Matrix"
