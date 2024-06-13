import Game.Metadata


World "Module"
Level 2

Title "Konkrete Vektorräume"

Introduction
"
Den $\\mathbb{Q}$-Vektorraum $\\mathbb{Q}^3$ definiert man am besten mit
der lokalen Notation

```
local notation `ℚ³` := Fin 3 → ℚ
```

Dabei ist `Fin 3` die Indexmenge $\\{0, 1, 2\\}$.

Die schreibweise für einen Vektor ist `![ _, _ ]`. Zu beachten ist,
dass man bei Zahlen explizit einen Typ angeben muss, sonst denkt sich
Lean, man arbeite über `ℕ`.

Um direkt Vektoroperationen über `ℚ` auszurechnen, kann man oft
`#eval` benutzen:

```
#eval ![ (2 : ℚ), 5 ] + ![ 1/2, -7 ]
```
zeigt `![5/2, -2]` an.

Um eine Gleichheit in einem Beweis zu verwenden, muss man andere Taktiken
benutzen.

Am hilfreichsten ist die kombination `funext i, fin_cases i`, die
Dann eine Vektorgleichung komponentenweise aufteilt.

Für jede Komponente kann man dann mit `simp` und `ring` weiterkommen.
"

local notation "ℚ³" => Fin 3 → ℚ
local notation "ℚ^(" n ")" => (Fin n) → ℚ

/--  -/
Statement : ![ (2 : ℚ), 5 ] + ![ 1/2, -7 ] = ![5/2, -2] := by
  funext i
  fin_cases i <;>
  simp <;>
  ring

NewTactic fin_cases
