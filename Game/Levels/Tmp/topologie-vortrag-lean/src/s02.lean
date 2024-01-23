import topology.basic
import topology.path_connected
import analysis.normed_space.basic
import data.set.basic

/-
### Beispiel 1.1.1: $S^2$

Damit wir die Sphäre $S^2$ als topologischen Raum definieren können,
benötigen wir die kanonische Norm auf $\mathbb{R}^3$. Diese ist
in dem Package
```
analysis.normed_space.basic
```
definiert.
-/

def S2 : set (ℝ × ℝ × ℝ) := { x | ‖x‖ = 1 }

/-
Wir haben jedoch noch keine Topologie auf dieser Menge.
Wir möchten hierfür die Unterraumtopologie von ℝ³ auf S² anwenden.
-/

#check topological_space.induced

instance : topological_space S2 :=
  let
    R3 := (by apply_instance : topological_space (ℝ × ℝ × ℝ)),
    i : S2 → ℝ×ℝ×ℝ := subtype.val
  in
  topological_space.induced i R3

-- alternativ:
--
-- def S2 : topological_space S2' :=
--   -- inklusion von S² in ℝ³
--   let i : ↥S2' → ℝ × ℝ × ℝ := subtype.val in
--   topological_space.induced i (by apply_instance : topological_space (ℝ × ℝ × ℝ))
--                                ↑↑↑↑↑↑↑↑↑↑↑↑↑↑
-- Hiermit möchten wir die kanonische topologie auf ℝ³ verwenden.

/-
### Beispiel 1.1.2: $[0,1]$
-/

def I : set ℝ := {x : ℝ | 0 ≤ x ∧ x ≤ 1}
instance : topological_space I :=
  let
    R := (by apply_instance : topological_space ℝ),
    i : ↥I → ℝ := subtype.val
  --    ↑
  -- Dieser Pfeil bedeutet, dass wir den "komplexen" Typen `(set.Icc (0 : ℝ) 1)`
  -- eigentlich als eine Instanz vom Typen `ℝ` betrachten wollen.
  -- Das betrachten von Typen als andere "ähnliche" Typen ist in Lean als
  -- "coercion" benannt: https://leanprover.github.io/functional_programming_in_lean/type-classes/coercion.html
  in
  topological_space.induced i (by apply_instance : topological_space ℝ)

/-
### Beispiel 1.1.3: $S^1 + S^1$

In diesem Fall möchten wir das Koprodukt von zwei Kreisen betrachten:
     *****           *****
   **     **       **     **
  *         *     *         *
 *           *   *           *
  *         *     *         *
   **     **       **     **
     *****           *****

Zuerst betrachten wir den Kreis als einen topologischen Raum
-/

-- Definition von S1, wie Sie es angegeben haben.
def S1 : set (ℝ × ℝ) := {x : ℝ × ℝ | ‖x‖ = 1}
instance : topological_space S1 :=
  let
    R2 := (by apply_instance : topological_space (ℝ × ℝ)),
    i : S1 → ℝ×ℝ := subtype.val
  in
  topological_space.induced i R2

-- alternativ
-- def S1 : topological_space {x : ℝ × ℝ | ‖x‖ = 1} :=
--   let
--     R2 := (by apply_instance : topological_space (ℝ × ℝ)),
--     i : {x : ℝ × ℝ | ‖x‖ = 1} → ℝ×ℝ := subtype.val
--   in
--   topological_space.induced i R2

/-
Nun möchten wir das Koprodukt bilden:
-/

def S1plusS1 : set (ℝ×ℝ) := {x: ℝ×ℝ | ‖x‖ =1} ∪ {x: ℝ×ℝ | ‖x-(2,0)‖ =1}
instance : topological_space S1plusS1 :=
  let
    R2 := (by apply_instance : topological_space (ℝ × ℝ)),
    i : S1plusS1 → ℝ×ℝ := subtype.val
  in
  topological_space.induced i R2
