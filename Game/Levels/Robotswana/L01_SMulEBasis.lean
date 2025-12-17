import Game.Metadata
import Game.Levels.Babylon

World "Robotswana"
Level 1

Title "" -- "Standardbasis"

/-
Introduction
"
Den Spuren folgend, findet ihr ein Stück Pergament, auf dem zuoberst
eine Notiz steht.

```
E i j := single i j (1 : ℝ)
```

Darunter ein bisschen wildes Gekritzel, das aber deutlich mit einer klaren
Zeile angefangen hat:
"
-/

Introduction "Intro Robotswana L01: introduce definition
```
E i j := single i j (1 : ℝ)
```
"

open Nat Matrix

def Matrix.E {n : ℕ} (i j : Fin n) : Mat[n,n][ℝ] :=
  single i j (1 : ℝ)

/-- `E i j` ist die `n × n`-Matrix (mit Werten in `ℝ`) mit einer `1` an
Stelle $(i, j)$ und Null überall sonst.

Dies ist eine spezialisierte Form der generellen `single i j (a : R)`,
welche auch nicht-quadratisch sein kann und einen beliebigen Wert `a` aus einem beliebigen
Ring annehmen kann. Wir benutzen hier `E` einfach als Abkürzung.
-/
DefinitionDoc Matrix.E as "E" in "Matrix"

/---/
TheoremDoc Matrix.smul_ebasis as "smul_ebasis" in "Matrix"

Statement Matrix.smul_ebasis {n : ℕ} (A : Mat[n,n][ℝ]) (i j) :
    A i j • E i j = single i j (A i j) := by
  /-
  Hint "**Du**: Welches Wesen auch immer hier Spuren hinterlassen hat – mir scheint, es mag Matrizen.
  Jedenfalls sieht `Mat[{n},{n}]` stark nach $({n} \\times {n})$-Matrizen aus.
  Ich weiß nur nicht mehr, was `Fin {n}` ist.

  **Robo**: `Fin {n}` war die Menge $\\\{0,…,n-1\\}$.
  Die Zeilen- und Spaltenindizes fangen hier also bei $0$ an und nicht bei $1$.
  Und `single i j a` kenne ich zufällig.
  Das ist die Matrix, die an der Position `(i, j)` den Eintrag `a` hat und sonst überall Null ist.

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
  -/
  Hint "`Mat[{n},{n}]` looks like a $({n} \\times {n})$ matrix. Reminder for `Fin {n}`: `Fin {n}` is
  the set $\\\{0,...,n-1\\}$. Indeces start here at $0$ and not $1$. `single i j a` is the matrix which
  has at position `(i, j)` the entry `a` and else zero. `E`s are abbreviations for case `a = 1`.
  `A i j` is entry of matrix `A` at position `(i, j)`. Goal can be seen as scalar multiplication akin to

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

  Begin with `unfold E`.
  "
  unfold E
  simp

/-
Conclusion "**Du**: Und was machen wir jetzt mit dieser „Erkenntnis“?

**Robo**: Keine Ahnung.  Ich speichere das jedenfalls mal als `Matrix.smul_ebasis` ab, falls wir es nochmals
brauchen.

Damit folgt ihr weiter der Spur.
"
-/
Conclusion "Conclusion Robotswana L01: Save result as `Matrix.smul_ebasis`"
NewDefinition Matrix.E

TheoremTab "Matrix"
