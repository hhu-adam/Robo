import Game.Metadata

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

import Game.Levels.Sum


World "Matrix"
Level 1

Title "Matrix"

-- TODO: Story

Introduction
"
[Es] fragt euch folgendes:

```
def FirstColumnSumZero {n : ℕ} [NeZero n] :
    Submodule ℝ (Mat[n,n][ℝ]) where
  carrier := {A | ∑ i, A i 0 = 0}
  add_mem' := sorry
  zero_mem' := sorry
  smul_mem' := sorry
```

**Du**: Also die Frage ist, ob die Menge aller `n×n`-Matrizen über $\\mathbb{R}$ mit der
ersten Spalte null auch wieder einen $\\mathbb{R}$-Vektorraum bildet. Aber wie gehe ich jetzt mit
dieser Struktur vor? Robo, kannst du mir helfen?

**Robo**: Klar, den Untervektorraum kann ich definieren, aber ich verstehe die Mathe nicht.
Hier sind die drei Goals die noch übrig sind:
"

-- **Robo**: In Lean sind Matrizen geschrieben als `Matrix (Fin n) (Fin m) R`. Ich kann dir aber
-- helfen und diese als `Mat[n,m][R]` darstellen.

open Nat Matrix BigOperators StdBasisMatrix Finset Set

-- `M` is flagged as unused.
set_option linter.unusedVariables false in

Statement FirstColumnSumZero
    (preamble := refine' { carrier := M, ..} <;> dsimp only)
    {n : ℕ} [NeZero n] :
    let M := {A : Mat[n,n][ℝ] | ∑ i, A i 0 = 0}
    Submodule ℝ Mat[n,n][ℝ] := by
  · Hint "**Du**: Ich verstehe, beim ersten müssen wir zeigen, dass `a + b` wieder in `M` ist."
    intro a b ha hb
    Hint "**Du**: Haben wir nicht schon gesehen, was dieses `∈ M` bedeutet?

    **Robo**: Wir hatten einmal `Set.mem_setOf`, das wird dir helfen!"
    rw [mem_setOf]
    Branch
      -- also possible:
      rw [mem_setOf] at *
    Branch
      -- Note: We delete `ha` and `hb` for the hints, so that the user sees the hints even
      -- if they are in the wrong form
      clear ha hb
      Hint "
      **Du**: also vermutlich will ich ja jetzt sagen, dass
      $({a} + {b})(i,j) = a(i,j) + b (i,j)$ ist.

      **Robo**: Das ist `Matrix.add_apply`. Und vergiss nicht, dass man unter Summen
      `simp_rw` verwenden muss anstatt `rw`!"
      simp_rw [Matrix.add_apply a b]
      Hint "**Du**: Darüber hatten wir mal auf Babylon geredet, wie hiess dass nochmals?"
      Hint (hidden := true) "**Robo**: `sum_add_distrib`."
      rw [sum_add_distrib]
      Hint (hidden := true) "**Robo**: Ob deine Annahmen wohl was nützen?"
    simp_rw [Matrix.add_apply a b]
    rw [sum_add_distrib]
    Branch
      -- not necessary but helps seeing what's going on
      Hint "**Robo**: Du könntest aber noch mit `rw [mem_setOf] at *` die Annahmen
      in die richtige Form bringen!"
      rw [mem_setOf] at *
    rw [ha, hb]
    simp
  · Hint "**Robo**: Dieses Goal verlangt, dass `0` in `M` liegt.

    **Du**: Ich würd wohl wie vorher gleich mit `mem_setOf` anfangen!"
    rw [mem_setOf]
    Hint (hidden := true) "**Robo**: Den Fall wo alles Null ist kann `simp` ganz gut!"
    simp
  · Hint "**Du**: Ah und das letzte Goal will dass `r • a` in `M` liegt!

    **Robo**: sieht ganz so aus!"
    intro c a ha
    Hint (hidden := true) "**Robo**: `mem_setOf`, dass weisst du doch schon!"
    rw [mem_setOf]
    Hint "**Du**: Ich weiss nicht, was ich mit der Skalarmultiplikation mache. eigenlich ist der
    innere Teil ja einfach `{c} • ({a} i 0)`.

    **Robo**: Das klingt nach einem Fall für `simp`!"
    simp?
    Hint "**Robo**: Meine Datenbank mit alten Konversationen sagt, dass wir mal `mul_sum`
    hatten auf Babylon."
    Hint "**Robo**: Du willst von rechts nach links umschreiben, also brauchst du hier
    ein `←mul_sum`."
    rw [← mul_sum]
    Branch
      -- not necessary but helps seeing what's going on
      Hint "**Robo**: Du könntest aber noch mit `rw [mem_setOf] at {ha}` die Annahmen
      in die richtige Form bringen!"
      rw [mem_setOf] at ha
    rw [ha]
    simp

Conclusion ""

/---/
TheoremDoc Matrix.add_apply as "Matrix.add_apply" in "Matrix"


-- TODO: Move
/-- Dieses Theorem sollte eigentlich woanders eingeführt werden -/
TheoremDoc Finset.mul_sum as "Finset.mul_sum" in "Matrix"



NewTheorem Matrix.add_apply Finset.mul_sum

TheoremTab "Matrix"
