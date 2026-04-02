import linear_algebra.matrix.determinant
import data.matrix.notation
import linear_algebra.matrix.general_linear_group
import algebra.big_operators.finprod

variables

open matrix
open_locale big_operators matrix

/-- An elementary matrix of type 1 or 3. if `i = j`, they are called "type 3" in literature,
otherwise "type 1". Note that "type 2" is not needed in this document, so we do not define it. -/
def matrix.E {R : Type} [field R] {n : ℕ} (i j : fin n) (a : Rˣ) : matrix (fin n) (fin n) R :=
  λ i₁ j₁, if i = i₁ ∧ j = j₁ then a else if i₁ = j₁ then 1 else 0

variables {R : Type} [field R] {n : ℕ} (i j : fin n) (a : Rˣ)

/-- Predicate for an arbitrary matrix to be elementary. -/
def is_elementary  (A : matrix (fin n) (fin n) R) : Prop :=
  ∃ i j a, A = matrix.E i j a

/-! ## Typ 2 Elementarmatrizen -/

/-- Typ 2 elementarmatrizen entsprechen dem vertauschen von Zeilen/Spalten. -/
def matrix.E₂ {R : Type} [field R] {n : ℕ} {i₁ i₂ j₁ j₂ : fin n}
    (hi : i₁ ≠ i₂) (hj : j₁ ≠ j₂) (a : Rˣ) : matrix (fin n) (fin n) R :=
  λ i j, if i = j then
    if (i = i₁ ∧ j = j₂) ∨ (i = i₂ ∧ j = j₁) then 0 else 1
  else
    if (i = i₁ ∧ j = j₂) ∨ (i = i₂ ∧ j = j₁) then 1 else 0

example (i₁ i₂ j₁ j₂ : fin 2) (hi : i₁ ≠ i₂) (hj : j₁ ≠ j₂) :
  (matrix.E₂ hi hj a) =
  (matrix.E i₁ j₁ (-1)) ⬝ (matrix.E i₂ j₁ 1) ⬝ (matrix.E i₁ j₂ (-1)) ⬝ (matrix.E i₂ j₁ 1) :=
begin
  unfold matrix.E₂,
  unfold matrix.E,
  ext i j,
  simp [mul_apply],
  sorry -- meh. hard. or is there a typo in the definition?
end

/-- If `i = j` then the elementary matrix is a diagonal matrix. -/
lemma eq_diagonal {R : Type} [field R] {n : ℕ} {i j : fin n} {a : Rˣ} (hij : i = j) :
  matrix.E i j a = diagonal (λ k, if i = k then a else 1) :=
begin
  ext i₁ j₁,
  unfold matrix.E,
  unfold diagonal,
  by_cases h : i₁ = j₁,
  { simp [if_pos h, hij, h] },
  { simp [hij, if_neg h],
    intros x y,
    rw x at y,
    exact h y, -- contradiction gives timeout?
    },
end

/-- The determinant of an elementary matrix is `1` (type 1) or `a` (type 3). -/
lemma elementary_det : (matrix.E i j a).det = if i = j then a else 1 :=
begin
  by_cases h : i = j,
  {
    rw [if_pos h],
    rw eq_diagonal h,
    simp,
  },
  {
    rw [if_neg h],
    sorry, -- der Teil ist aufwendiger. mit oberen/unteren Dreiecksmatrizen.
  },
end

/-- Any elementary matrix is invertible. -/
lemma elementary.is_unit (R : Type) [field R] {n : ℕ} (j i : fin n) (a : Rˣ) :
  is_unit (matrix.E i j a) :=
begin
  rw [matrix.is_unit_iff_is_unit_det],
  rw [elementary_det],
  by_cases h : i = j,
  { rw [if_pos h],
    simp },
  { rw [if_neg h],
    simp },
end

variables (n) (R)

abbreviation elementary_matrices := {A : GL (fin n) R | is_elementary A}

variable (A : fin n → matrix (fin n) (fin n) R)

/-- Any invertible matrix is a product of elementary matrices. -/
theorem invertible_product_elementary (A : GL (fin 3) R) :
  ∃ M : list (matrix (fin 3) (fin 3) R), M.foldr (*) 1 = A ∧ (∀ B ∈ M, (is_elementary B)) :=
begin
  sorry -- nah, that's equivalent to Gauss-elimination and would rather need
  -- a dedicated tactic implementing gauss elimination…
end



#check finsupp.lsingle
#check finsupp.lapply

#check linear_map.single
#check linear_map.proj

namespace snd_attempt

variables {R : Type} [field R] {n : ℕ}

def E  (i j : fin n) (a : Rˣ) : matrix (fin n) (fin n) R :=
  λ i₁ j₁, if i = i₁ ∧ j = j₁ then a else if i₁ = j₁ then 1 else 0


end snd_attempt