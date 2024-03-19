--import Game.Metadata
import GameServer.Commands

import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic


import Game.StructInstWithHoles

set_option tactic.hygienic false

World "Matrix"
Level 1

Title "Matrix"

Introduction
"
The `n`-dim vectors form a vector space.
"

instance (n : ℕ) : Module ℝ ((Fin n) → ℝ) where
  smul := by
    intro r v
    exact fun i => r * v i
  one_smul := by
    intro v
    funext i
    exact one_mul (v i)
  mul_smul := by
    intro r s v
    funext i
    exact mul_assoc r s (v i)
  smul_zero := by
    intro r
    funext i
    exact mul_zero r
  smul_add := by
    intro r v w
    funext i
    exact mul_add r (v i) (w i)
  add_smul := by
    intro r s v
    funext i
    exact add_mul r s (v i)
  zero_smul := by
    intro v
    funext i
    exact zero_mul (v i)


#check 2 • ![1,1]
#eval 2 • ![1,1]


/- Show that adding zero to a the tail of a vector is a linear map. -/

#check Function.update
#check Function.extend
#check Function.ExtendByZero.hom
#check Function.extend_add

example (i : Fin n) : Fin (n + 1) := i

@[simp] noncomputable
def extendByZero {n : ℕ} (v : (Fin n) → ℝ) : (Fin (n+1) → ℝ) :=
  by
  refine Function.extend (fun (i : Fin n) => (i: Fin (n+1))) ?_ ?_
  exact v
  exact 0

def extendByZero' {n : ℕ} (v : (Fin n) → ℝ) : (Fin (n+1) → ℝ) :=
  fun i => if h : i.val < n then v ⟨i.val, h⟩ else 0

/- We now prove that `extendByZero` is an ℝ-linear map. -/
noncomputable

def extendByZeroLinear : ( (Fin n) → ℝ ) →ₗ[ℝ] (Fin (n+1) → ℝ) where
  toFun := extendByZero
  map_add' := by
    intro v w
    funext i
    simp
    conv =>
      lhs
      rw [← add_zero 0]
      simp only [Function.extend_add]
  map_smul' := by
    intro r v
    funext i
    simp
    conv =>
      lhs
    sorry


-- example : 2 • ![(1 : ℝ),1,0] = ![(2 : ℝ),2,0] := by
--   apply extendByZeroLinear.map_smul' --fails, a bug?
--   sorry
