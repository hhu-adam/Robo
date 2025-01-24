import algebra.algebra.basic
import data.matrix.basic
import linear_algebra.matrix.determinant
import algebra.ring.basic
import algebra.char_p.basic
import algebra.is_prime_pow
import linear_algebra.matrix.general_linear_group
import data.rat.basic
import data.real.basic
import analysis.normed_space.exponential
import analysis.special_functions.log.basic
import linear_algebra.matrix.block
import data.finsupp.basic

def A (n: ℕ) : Type := matrix.general_linear_group (fin n) ℚ

open classical


variables {n : Type*} [fintype n] [decidable_eq n]
variables {R : Type*} [comm_ring R]

def absolute_valu (x : ℝ) : ℝ :=
abs x

-- General Linear Group
abbreviation GL_fake (n:Type* )[fintype n] [decidable_eq n] (R : Type) [comm_ring R]: Type*:=
(matrix n n R)ˣ

-- Zentrum der General Linear Group GL(n, R)
def center_GL  (n:Type* )[fintype n] [decidable_eq n] :=
 { A : matrix n n ℚ | ∀ B :  (GL_fake n ℚ), matrix.mul A  B = matrix.mul B  A }

-- Einheitsmatrix
#check (1 : matrix n n R)
variable (R)

/-! Wir benötigen die Matrix die auf der Diagonale und auf einem nicht-diagonalen Eintrag
eine 1 hat, da diese in GL liegt. Diese heisst hier `oneP_of` und ist `1 + single_one`. -/

/-- Matrix with 0s everywhere and a single 1. -/
def single_one (R : Type*) [comm_ring R] (k l : n) : matrix n n R :=
λ i j, if i = k ∧ j = l then 1 else 0

#check pi.single_apply

lemma single_one_apply₁ (k l i: n) : single_one R k l i = if i = k then pi.single l 1 else 0:=
begin
  -- ext, by_cases, single_one, pi.single_apply
  ext j,
  by_cases h : i = k,
  { rw [h, if_pos rfl, single_one],
    rw pi.single_apply,
    dsimp,
    by_cases hj : j = l,
    {
      rw ← hj,
      simp,
    },
    simp,
  },
  rw single_one,
  simp_rw pi.single_apply,
  rw [if_neg, if_neg],
  refl,
  assumption,
  assume h₁,
  have hk : i = k, from h₁.left,
  have hl : j = l, from h₁.right,
  contradiction,

end

lemma single_one_apply₂ (k l j : n) : (λ i, single_one R k l i j) = if j = l then pi.single k 1 else 0:=
begin
  -- ext, by_cases, single_one, pi.single_apply
  ext i,
  by_cases hj : j = l,
  {
    rw [if_pos hj],
    rw [single_one],
    rw [pi.single_apply],
    by_cases hi : i = k,
    {
      rw [if_pos hi],
      rw hi,
      rw hj,
      simp,
    },
    {
      by_cases h₁ : i = k,
        { -- Fall: i = k
          rw [h₁, hj],
          simp,
        },
        { -- Fall: i ≠ k
          rw if_neg hi,
          simp,
          contradiction,
        },
    },
  },
  {
    rw [if_neg hj],
    rw [single_one],
    by_cases h₁ : i = k,
    {
      rw [h₁],
      rw if_neg hj,
      refl,
    },
    { simp only [ite_false],
      intro h,
      apply h₁,
      exact h
    }
  },
end

open_locale matrix

lemma mul_single_one (A : matrix n n R) (k l : n) :
  A ⬝ single_one R k l = (λ i j, if j = l then A i k else 0) :=
begin
  -- single_one_apply₂, matrix.mul,
  -- ext, by_cases j = l
  sorry
end


lemma single_one_mul (A : matrix n n R) (k l : n) :
  single_one R k l ⬝ A = (λ i j, if i = k then A l j else 0) :=
begin
  -- single_one_apply₁, matrix.mul,
  -- ext, by_cases i = k
  sorry
end

/-- Matrix with 1s on the diagonal, one 1 off the diagonal, and 0s elsewhere.
    Special case: if `k = l`, we get a matrix with 1s on the diagonal, and one 2 on the diagonal, 0s elsewhere. -/
def one_off (R : Type*) [comm_ring R] (k l : n) := single_one R k l + 1

lemma mul_one_off (A : matrix n n R) (k l : n) :
  A ⬝ one_off R k l = (λ i j, if j = l then A i k else 0) + A :=
begin
  -- [matrix.mul_add, mul_single_one],
  sorry
end

lemma one_off_mul (A : matrix n n R) (k l : n) :
  one_off R k l ⬝ A = (λ i j, if i = k then A l j else 0) + A :=
begin
  -- matrix.add_mul, single_one_mul
  sorry
end

lemma is_unit_one_off (k l : n) : is_unit (one_off R k l) :=
begin
  sorry
end
-- Das sollte man mit diesen Lemmas zeigen können:
#check matrix.det_of_upper_triangular
#check matrix.det_of_lower_triangular
#check matrix.is_unit_iff_is_unit_det

variable (n)

-- Ich habe aus Convenience das Zentrum von GLn nochmals anders definiert:
def center := {A : matrix n n R | ∀ (B : matrix n n R), is_unit B → A ⬝ B = B ⬝ A }

variable {n}

-- Jede Matrix im Zentrum ist diagonal
lemma center_diagonal {A : matrix n n R} (h : A ∈ center n R) (i j : n) (hij : i ≠ j) : A i j = 0 :=
begin
  have h₂ : ∀ k l, (A ⬝ one_off R j i) k l = (one_off R j i ⬝ A) k l,
  { intros k l,
    rw h (one_off R j i) (is_unit_one_off R _ _) },
  replace h₂ := h₂ i i,
  simp [mul_one_off, one_off_mul, hij] at h₂,
  assumption,
end

lemma center_diagonal_all_equal {A : matrix n n R} (h : A ∈ center n R) (i j : n) : A i i = A j j :=
begin
  -- Analog zu oben
  sorry
end

-- Beweis, dass das Zentrum die skalaren Matrizen sind
theorem center_GL_eq_scalar_matrices (n : ℕ):
center (fin n) ℚ = { A : matrix (fin n) (fin n) ℚ | ∃ (D : ℚ), A = D • (1 : matrix (fin n) (fin n) ℚ) } :=
begin
  ext,
  constructor,
  {
    -- Diese Richtung ist massiv schwieriger. Ich habe diese weitgehend
    -- ausgefüllt, so dass du dich auf die `sorry` oben beschränken
    -- kannst.
    intro h,

    -- Das sind die beiden Hauptresultate von oben.
    have h₁ := center_diagonal ℚ h,
    have h₂ := center_diagonal_all_equal ℚ h,

    rw [set.mem_set_of] at *,
    cases n,
    { -- case `0`
      simp,
    },

    -- Da `h₂` sagt, dass alle Diagonaleinträge von `x` gleich sind, können
    -- wir den ersten nehmen
    use x 0 0,

    -- Da `ext` ja zu viele ext-Lemmas anwendet.
    ext1,

    by_cases k : i = j,
    {
      rw [k],
      simp,
      apply h₂,
    },
    {
      replace h₁ := h₁ i j k,
      rw [h₁],
      simp,
      right,
      rw [matrix.one_apply_ne],
      assumption,
    }
  },
  {
    -- Die Richtung ist relativ einfach.
    -- `rw [set.mem_set_of] at *` hilft.
    rw [set.mem_set_of] at *,
    intro h,
    intro h₁,
    cases h with D hx,
    rw hx,
    rw matrix.smul_mul,
    rw matrix.mul_smul,
    intros hu,
    cases hu with u hu,
    rw ←hu,
    rw matrix.mul_one,
    rw matrix.one_mul,

  }
  end