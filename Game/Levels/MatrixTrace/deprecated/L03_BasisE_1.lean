-- import Game.Metadata
import GameServer.Commands

import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Trace

import Mathlib

notation R"^"n" × "m => Matrix (Fin n) (Fin m) R

World "Trace"
Level 3

Title "Trace"

Introduction
"
The matrices `E i j` are defined as the matrix with a 1 at position `i, j` and 0 elsewhere. In below, `E i j` are defined in terms of mathlib's `stdBasisMatrix`.

`stdBasisMatrix i j c` is the matrix with `c` at position `i, j` and 0 elsewhere.

"

open Nat Matrix BigOperators StdBasisMatrix

#check Matrix

#check stdBasisMatrix

#check StdBasisMatrix.mul_right_apply_same

#check trace_mul_comm

abbrev E {n : ℕ} (i j : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  stdBasisMatrix i j 1

lemma trace_eq_one {i : Fin n} : trace (E i i) = 1 := by
  simp only [trace_eq]

lemma E_mul_E {n : ℕ} {i j k : Fin n} : E i j * E j k = E i k := by
  simp only [mul_same, mul_one]

lemma E_mul_E_ne {i j k l : Fin n} (h : j ≠ k) :
    E i j * E k l = 0 := by
  exact mul_of_ne i j 1 h 1

#check matrix_eq_sum_std_basis

#check Matrix.one

#check Finset.sum_subset

#check ne_of_mem_of_not_mem
#check Set.singleton
#check Set



lemma tmp1 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i j) : A i j • E i j = stdBasisMatrix i j (A i j) := by
  simp only [smul_stdBasisMatrix]
  simp only [smul_eq_mul, mul_one]
