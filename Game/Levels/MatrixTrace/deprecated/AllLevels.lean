import GameServer.Commands

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

import Game.Levels.Sum

import Game.Metadata.StructInstWithHoles

set_option tactic.hygienic false

World "Matrix"
Level 2

Title "Matrix"


Introduction
"
The collection `ℝ^(m×n)` of `m × n` matrices with real-valued entries forms a vector space over `ℝ`.
In this level you prove that the collection of square matrices of size `n × n` with the property that the sum of whose first column is zero forms a subspace of `ℝ^(n×n)`.
"

-- Bemerkungen:
-- 1) An m×n matrix with entries in `ℝ` is a function `Fin m → Fin n → ℝ`.
-- 2) The type of m×n matrices with entries in `ℝ` is `Matrix (Fin m) (Fin n) ℝ`.
-- 3) We use the notatoin `ℝ^(m×n)` for `Matrix (Fin m) (Fin n) ℝ` since it has better compatibility with the column-vector and row-vector matrices.
-- 4) The empty square matrix is the unique function `Fin 0 → Fin 0 → ℝ`.
-- 5) Given a square matrix `A` of size `n × n`, the diagonal `diag A` is a vector `n → α` such that `(diag A) i = A i i`.
-- 6) Given a square matrix `A` of size `n × n`, the trace `tr A` is the sum of the diagonal entries of `A`.

-- we should not need noncomputable here but it seems Lean is using an instance of RorC through the inner product instance here.
noncomputable
instance (n : ℕ) : Module ℝ (Matrix (Fin n) (Fin n) ℝ) := by infer_instance

#synth Module ℝ (Matrix (Fin 2) (Fin 2) ℝ)

#check Submodule

whatsnew in
theorem foo : 42 = 6 * 7 := rfl

-- Remark: maybe we should introduce `funext` or `ext` before if we have not done so.
instance (n : ℕ) : Module ℝ (Matrix (Fin n) (Fin n) ℝ) where
  smul := fun r A i j => r * A i j --r • A i j  -- Pi.instSMul
  one_smul := by -- simp
    intro A
    funext i j
    dsimp
    rw [one_mul] --?
  mul_smul := by
    intro x y A
    funext i j
    dsimp
    rw [mul_assoc] --?
  smul_zero := by
    intro r
    funext i j
    dsimp
    rw [mul_zero] --?
  smul_add := by
    intro r A B
    funext i j
    dsimp
    rw [mul_add] --?
  add_smul := by
    intro r s A
    funext i j
    dsimp
    rw [add_mul] --?
  zero_smul := by
    intro A
    funext i j
    dsimp
    rw [zero_mul] --?

#check LinearMap.toMatrix



Introduction
"
The collection `ℝ^(m×n)` of `m × n` matrices with real-valued entries forms a vector space over `ℝ`.
In this level you prove that for `n > 0` the collection of square matrices of size `n × n` with the property that the sum of whose first column is zero forms a subspace of `ℝ^(n×n)`.

In Lean we provide a submodule structure by filling in the holes of the following structure:
```
def FirstColumnSumZero {n : ℕ} [NeZero n] : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) where
   carrier := fun A => ∑ i, A i 0 = 0
   add_mem' := sorry
   zero_mem' := sorry
   smul_mem' := sorry

```

"

open Nat Matrix BigOperators StdBasisMatrix Finset

-- Bemerkungen:
-- 1) An m×n matrix with entries in `ℝ` is a function `Fin m → Fin n → ℝ`.
-- 2) The type of m×n matrices with entries in `ℝ` is `Matrix (Fin m) (Fin n) ℝ`.
-- 3) We use the notatoin `ℝ^(m×n)` for `Matrix (Fin m) (Fin n) ℝ` since it has better compatibility with the column-vector and row-vector matrices.
-- 4) The empty square matrix is the unique function `Fin 0 → Fin 0 → ℝ`.


def first_column_sum_zero' {n : ℕ} [NeZero n] : Set (Matrix (Fin n) (Fin n) ℝ) :=
  fun A => ∑ i, A i 0 = 0

Statement FirstColumnSumZero'
    (preample := refine { carrier := M, ?..} <;> dsimp only)
    {n : ℕ} [NeZero n] :
    let M := {A : Matrix (Fin n) (Fin n) ℝ | ∑ i, A i 0 = 0}
    Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) := by
  Hint "Wir müssen jetzt die drei Axiome eines Untermoduls `S` zeigen:

  * Abgeschlossenheit unter `+`
  * Enthält `0`
  * Abgeschlossenheit unter `•`.

  Wir fangen mit dem ersten an:

  `intro A B hA hB`
  "
  · intro A B hA hB
    Hint (hidden := true) "
      A definitionally equal goal is `(∑ i, ({A} + {B}) i 0 ) = 0`.
      Tactic `change` can be used to change the goal to this.
      However, strictly speaking, this is not necessary since `simp` sees through such equalities."
    Branch
      change (∑ i, (A + B) i 0 ) = 0
    Hint (hidden := true) "`add_apply {A} {B}` simplifies the pointwise addition of two matrices."
    simp [add_apply A B]
    Hint (hidden := true) "`rw [sum_add_distrib]`"
    rw [sum_add_distrib]
    Hint (hidden := true) "`rw [{hA}, {hB}, zero_add]`"
    rw [hA, hB, zero_add]
  · Hint (hidden := true) "somwhat ugly…

    This is because `Submodule` consists of `AddSubmonoid` and `SubMulAction`.

    here we show that `0 ∈ (M, +)` as a submonoid.

    `simp`"
    simp
  · Hint "Oh god, is this ugly!

    similar reason as above, a simple `dsimp only` also brings this into a readably form

    `simp`"
    simp
    Hint "`intro c A hA`"
    intro c A hA
    Hint "`rw [← Finset.mul_sum]`"
    rw [← Finset.mul_sum]
    Hint "`rw [hA]`"
    rw [hA]
    Hint "`simp`"
    simp


NewTheorem Finset.mul_sum zero_add Finset.sum_add_distrib Matrix.add_apply
NewTactic change refine

Introduction
"
The matrix `E i j` is defined as the matrix with a `1` at position `i, j` and `0` elsewhere. They are extemely sparse. In below, `E i j` are defined in terms of mathlib's `stdBasisMatrix`.

`stdBasisMatrix i j c` is the matrix with `c` at position `i, j` and `0` elsewhere.  `stdBasisMatrix` matrices are closed under scalar multiplication, becasue
`c • stdBasisMatrix i j 1 = stdBasisMatrix i j c`, a theorem witnessed by `smul_stdBasisMatrix`.

"

open Nat Matrix BigOperators StdBasisMatrix

abbrev E {n : ℕ} (i j : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  stdBasisMatrix i j 1

Statement smul_ebasis {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i j) : A i j • E i j = stdBasisMatrix i j (A i j) := by
  simp only [smul_stdBasisMatrix]
  simp only [smul_eq_mul, mul_one]

NewTheorem Matrix.smul_stdBasisMatrix mul_one smul_eq_mul smul_ebasis

Introduction
"
`stdBasisMatrix i j c` spans the vector space of matrices of a given size. This is witnessed by `matrix_eq_sum_std_basis`. In this level, you will show that the identity matrix is the sum of the matrices `E i i`.

"

open Nat Matrix BigOperators StdBasisMatrix

-- Not used later on in our proofs, but possibly useful and can be safely removed, or given as a hint
lemma tmp0 {n : ℕ} {i : Fin n} :
    E i i = stdBasisMatrix i i ((1 : Matrix (Fin n) (Fin n) ℝ) i i) := by
  rw [one_apply_eq]

Statement ebasis_diag_sum_eq_one {n : ℕ} : ∑ i : Fin n, E i i = 1 := by
  rw [matrix_eq_sum_std_basis 1]
  congr
  ext i r s
  rw [← Finset.sum_subset (s₁ := {i}) (Finset.subset_univ {i})]
  · simp only [Finset.sum_singleton, one_apply_eq]
  · intro x h₁ h₂
    have h₃ : i ≠ x := by
      simp [Finset.mem_singleton] at h₂
      symm
      exact h₂
    simp [one_apply, if_neg h₃]


NewTheorem Matrix.one_apply Finset.mem_singleton ebasis_diag_sum_eq_one

Introduction
"
The trace of a square matrix is the sum of the elements on its main diagonal. It is a linear map from the space of square matrices to the field of scalars. The lineariry is witnessed by the term `traceLinearMap` in Mathlib.

In Mathlib, trace is defined as the sum of the entries in the diagonal vector of a matrix:

```
∑ i, diag A i
```

where `diag A i = A i i`. You can prove `trace A = ∑ i, A i i` by `rfl`.

The trace of a identity matrix is the dimension of the matrix:

```
trace_one : trace (1 : Matrix α α ℝ) = Fintype.card α
```

Since `Fin n` has `n` elements, we have:

```
trace (1 : Matrix (Fin n) (Fin n) ℝ) = n
```

Use `trace_add` and `trace_sub` are special cases of the linearity of the trace which state that the trace of the sum of two matrices is the sum of their traces, and the trace of the difference of two matrices is the difference of their traces.

"

open Matrix BigOperators

Statement {n : ℕ} {t : ℝ} (A : Matrix (Fin n) (Fin n) ℝ) :
    trace (A - t • 1) = trace A - t * n := by
  rw [trace_sub]
  rw [trace_smul]
  rw [trace_one]
  rw [Fintype.card_fin]
  rfl

NewTheorem Fintype.card_fin Matrix.trace_one Matrix.trace_smul Matrix.trace_sub


Introduction
"
A linear functional `f` on the space of `n × n` matrices (for non-zero `n`) which kills
all commutators and moreover satisfies `f(1) = n` has the property that `f (E i i) = 1`
for all `i : Fin n`.
"

open Nat Matrix BigOperators StdBasisMatrix Finset

Statement eq_sum_apply_diag_ebasis {n : ℕ} {f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ}
    (h : ∀ i j, i ≠ j → f (E i j) = 0)
    (A : Matrix _ _ ℝ) :
    f A = ∑ i : Fin n, (A i i) * f (E i i) := by
  nth_rw 1 [matrix_eq_sum_std_basis A]
  simp_rw [map_sum]
  simp_rw [← smul_ebasis]
  simp_rw [LinearMap.map_smul]
  trans ∑ i : Fin n, ∑ j : Fin n, if i = j then (A i j) * f (E i j) else 0
  congr
  ext i
  congr
  ext j
  by_cases h₁ : i = j
  · rw [if_pos h₁]
    subst h₁
    rfl
  · rw [if_neg h₁]
    simp [h]
    right
    apply h
    assumption
  simp only [sum_ite_eq]
  simp only [sum_ite_mem]
  simp only [inter_self]


Introduction
"
The commutator of two matrices is defined as the difference between their product and the product
of the matrices in the opposite order, that is the commutator of `A` and `B` is `A * B - B * A`.
A linear functional `f` on the space of `n × n` matrices which kills all commutators has the same value on all the diagonal elemantary basis matrices, i.e. `f (E i i) = f (E j j)` for all `i` and `j`.
"

open Nat Matrix BigOperators StdBasisMatrix

Statement eq_on_diag_ebasis {n : ℕ} {f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ}
    (h : ∀ A B, f (A * B) = f (B * A))  :
    ∀ (i j : Fin n), f (E i i) = f (E j j) := by
  intro i j
  trans f (E i j * E j i)
  · rw [mul_same, mul_one]
  · rw [h, mul_same, mul_one]


Introduction
"
In this level, we will show that a linear functional `f` on the space of matrices which kills all commutators also kills all off-diagonal elementary basis matrices.
"

open Nat Matrix BigOperators StdBasisMatrix

-- H2
Statement zero_on_offdiag_ebasis {n : ℕ} {f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ}
    (h₁ : ∀ A B, f (A * B) = f (B * A)) :
    ∀ (i j : Fin n ), (i ≠ j) → f (E i j) = 0 := by
  intro i j hne
  trans f (E i j * E j j)
  · rw [mul_same, mul_one]
  · rw [h₁]
    rw [mul_of_ne j j 1 hne.symm 1]
    simp


Introduction
"
A linear functional `f` on the space of `n × n` matrices (for non-zero `n`) which kills
all commutators and moreover satisfies `f(1) = n` has the property that `f (E i i) = 1`
for all `i : Fin n`.
"

open Nat Matrix BigOperators StdBasisMatrix

#check NeZero

Statement one_on_diag_ebasis {n : ℕ} {f : Matrix (Fin n.succ) (Fin n.succ) ℝ →ₗ[ℝ] ℝ}
    (h₁ : ∀ A B, f (A * B) = f (B * A)) (h₂ : f 1 = n.succ) :
    ∀ i, f (E i i) = 1 := by
  intro i
  apply nat_mul_inj'
  have : n.succ * f (E i i) = f ( (n.succ : ℝ) • E i i) := by
    --unfold E
    rw [LinearMap.map_smul f]
    simp only [smul_eq_mul]
  rw [this]
  trans f (∑ _i : Fin n.succ, E i i)
  · congr
    rw [Fin.sum_const n.succ]
    simp only [smul_stdBasisMatrix]
    simp only [smul_eq_mul]
    simp only [mul_one]
    simp only [nsmul_eq_mul]
    simp only [cast_add, cast_one, mul_one]
  · rw [map_sum f (fun x => E i i) Finset.univ]
    --rw [apply_ebasis_diag h₁]
    trans ∑ i : Fin n.succ, f (E i i)
    · congr
      ext j
      simp only [eq_on_diag_ebasis  h₁ i j]
    · rw [← map_sum f (fun x => E x x) Finset.univ]
      rw [ebasis_diag_sum_eq_one]
      simp only [h₂]
      simp
  simp


/- Statements about linear maps and sums. -/


#check mul_eq_mul_left_iff


/- The Statement -/

#check (![] : Matrix (Fin 0) (Fin 0) ℝ) = 0

-- example {n : ℕ} (f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ) : ↑ f = f.toFun := rfl

Statement trace_eq {n : ℕ} (f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ)
    (h₁ : ∀ A B, f (A * B) = f (B * A)) (h₂ : f 1 = n) :
    trace = f := by
  ext A
  rw [eq_sum_apply_diag_ebasis (zero_on_offdiag_ebasis h₁)]
  rcases n
  · simp
  · simp_rw [eq_on_diag_ebasis h₁ _ 0]
    rw [← sum_mul]
    rw [one_on_diag_ebasis h₁ h₂ 0]
    simp [trace]


#check Matrix
#check stdBasisMatrix
#check StdBasisMatrix.mul_right_apply_same
#check trace_mul_comm



lemma trace_eq_one {n : ℕ} {i : Fin n} : trace (E i i) = 1 := by
  simp only [StdBasisMatrix.trace_eq]


lemma E_mul_E {n : ℕ} {i j k : Fin n} : E i j * E j k = E i k := by
  simp only [mul_same, mul_one]

lemma E_mul_E_ne {n : ℕ} {i j k l : Fin n} (h : j ≠ k) :
    E i j * E k l = 0 := by
  exact mul_of_ne i j 1 h 1

#synth Mul (Matrix (Fin 3) (Fin 3) ℝ)


lemma mul_tranpose_diag_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    diag (A * Aᵀ) i = ∑ k, (A i k)^2 := by
  simp only [transpose, pow_two]
  rfl

lemma trace_transpose_mul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ trace (A * Aᵀ) := by
  simp only [trace]
  simp only [transpose]
  simp only [Matrix.diag]
  simp only [Matrix.mul_apply]
  simp only [of_apply]
  simp only [← pow_two] -- positivity fails! A bug? something to improve?
  positivity
