-- Level name : Überabzählbarkeit von ℝ

import linear_algebra.dimension
import linear_algebra.finite_dimensional
import field_theory.cardinality
import data.real.basic
import data.real.cardinality
import set_theory.cardinal.basic

universe u

-- Damit man `#K` anstatt `cardinal.mk K` für die Kardinalität von `K` schreiben kann
open_locale cardinal

-- ℵ₀ is die Kardinalität von ℕ.
-- Die Kardinalität eines VR ist gleich derjenigen des Körpers falls eine endliche Basis existiert.
-- (Dieses Resultat kann gerne ge`sorry`ed bleiben
lemma cardinal_eq_of_finite_basis
  {K V : Type u} {ι : Type u} [field K] [add_comm_group V] [module K V] [fintype ι]
  (h : #K = cardinal.aleph_0) (h2: basis ι K V) :
  #V ≤ cardinal.aleph_0 :=
begin
  -- Schreibe `V` als Funktion `ι → K` (`ι` ist eine Basis), weil
  -- wir dann `cardinal.power_def` benützen können.
  rw cardinal.mk_congr (h2.equiv_fun.to_equiv),

  sorry,
  -- Ebenfalls hilfreich: `cardinal.power_nat_le`
end

-- Resultat, dass ℝ nicht abzählbar ist 
#check cardinal.not_countable_real

-- Eine Menge ist abzählbar gdw ihre Kardinalität `≤ ℵ₀` ist
#check cardinal.le_aleph_0_iff_set_countable

-- Hilfslemma
#check cardinal.mk_univ


/- Lemma
Zeige dass ℝ kein endlich dimensionaler ℚ-Vektorraum ist.
-/
example : ¬finite_dimensional ℚ ℝ :=
begin
  -- Die Basis von `ℝ` über `ℚ`
  set B := basis.of_vector_space ℚ ℝ,

  by_contradiction,
  -- Hint: das fügt `h: finite_dimensional ℚ ℝ` zum Instance-cache hinzu damit
  --Lean es später im Beweis automatisch findet.
  resetI,

-- Mein Teil

  -- Schreibe die Kardinalität von `ℚ` als ℵ₀
  have h_ℚ : #ℚ = cardinal.aleph_0:= cardinal.mk_eq_aleph_0 ℚ,
  --Warum geht das nicht?
  
  -- Anwenden des Lemmas auf die Basis `B` von `ℝ` über `ℚ`
  have cardinal_ineq : #ℝ ≤ cardinal.aleph_0 :=
    cardinal_eq_of_finite_basis h_ℚ B,

  -- Widerspruch
  have contradiction : false :=
    not_le.mpr (cardinal.not_countable_real) cardinal_ineq,

  exact contradiction,

  --sorry,

  -- Ende mein Teil
end
