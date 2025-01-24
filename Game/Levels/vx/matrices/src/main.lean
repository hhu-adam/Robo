import linear_algebra.matrix.determinant
import data.vector

variables {α : Type*} [field α] [decidable_eq α]

def diagonal_to_list (n:ℕ ) (A : matrix (fin n) (fin n) α ) : list α  :=
  list.map (λ i, A i i) (list.fin_range n)

def check_Typ_3 (n:ℕ ) (A : matrix (fin n) (fin n) α ): bool :=
  let AA := A - (matrix.diagonal A.diag) in 
  if AA=0 then
    if (list.countp (eq 1)  (diagonal_to_list n A)) = n-1 then
      true
    else
      false
  else
    false

def check_Typ_2 (n:ℕ ) (A : matrix (fin n) (fin n) α ): bool :=
  let row_to_list (i : fin n) : list α := list.map (λ j, A i j) (list.fin_range n) in
  if ∀ i : fin n, (list.countp (eq 1) (row_to_list i)) = 1 ∧ 
  list.countp (eq 0) (row_to_list i) = n-1 then
    true
  else
    false

def check_Typ_1 (n:ℕ ) (A : matrix (fin n) (fin n) α ): bool :=
  let AA := A-(matrix.diagonal A.diag) in
  if A.diag = 1 then
    if (list.countp (eq 0)  (diagonal_to_list n AA)) = n*n-1 then
      true
    else
      false
  else
    false


def is_elementary (n:ℕ ) (A : matrix (fin n) (fin n) α ) : bool :=
  if check_Typ_3 n A then
    true
  else 
    if check_Typ_1 n A then
      true
    else
      if check_Typ_2 n A then
        true
      else
        false


theorem invertible_prod_of_elementary (n: ℕ )  (M : matrix (fin n) (fin n) α) (h : invertible M) :
   ∃ matrices : list (matrix (fin n) (fin n) α), ∀ A, A ∈ matrices → is_elementary n A  :=
  begin
    
  end
  
