import Mathlib
-- mathlib PR: ………
theorem Set.subset_iff {A : Type} {s₁ s₂ : Set A} : s₁ ⊆ s₂ ↔ ∀ {x : A}, x ∈ s₁ → x ∈ s₂ := by
  rfl

-- Is scoped in CharZero
attribute [simp] CharZero.neg_eq_self_iff

-- mathlib PR: #19255
-- alias _root_.Nat.prime_def := Nat.prime_def_lt''


/-- Icc_insert lemmas
    - for ℤ, need very general version Finset.insert_Icc_ …
      One exercise in Babylon will use this!
    - for ℕ, there's a dedicated version Nat.Icc_insert …, which I current
      This is the version currently proved in Luna.
--/


/- The following lemmas are already included in newer versions of mathlib, in general forms that apply to both ℕ and ℤ:

   `Finset.insert_Icc_eq_Icc_add_one_right` -- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Order/Interval/Finset/SuccPred.html#Finset.insert_Icc_eq_Icc_add_one_right
   `Finset.insert_Icc_eq_Icc_sub_one_left`  -- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Order/Interval/Finset/SuccPred.html#Finset.insert_Icc_eq_Icc_sub_one_left
   `Finset.insert_Icc_add_one_left_eq_Icc`  -- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Order/Interval/Finset/SuccPred.html#Finset.insert_Icc_add_one_left_eq_Icc
   `Finset.insert_Icc_sub_one_right_eq_Icc` -- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Order/Interval/Finset/SuccPred.html#Finset.insert_Icc_sub_one_right_eq_Icc

   As a temporary solution, we provide two separate versions – one for ℕ and one for ℤ – of each lemma,
   in custom namespaces Robo.NN and Robo.ZZ. We open one of these namespaces whenever the theorems are required,
   so that the user does not notice that there are two different versions in the background.
-/
theorem Robo.NN.Finset.insert_Icc_eq_Icc_add_one_right {a b : ℕ} (h : a ≤ b + 1) :
insert (b + 1) (Finset.Icc a b) = Finset.Icc a (b + 1) := by
  ext x
  simp only [Finset.mem_insert, Finset.mem_Icc]
  omega

theorem Robo.ZZ.Finset.insert_Icc_eq_Icc_add_one_right {a b : ℤ} (h : a ≤ b + 1) :
insert (b + 1) (Finset.Icc a b) = Finset.Icc a (b + 1) := by
  ext x
  simp only [Finset.mem_insert, Finset.mem_Icc]
  omega

theorem Robo.NN.Finset.insert_Icc_eq_Icc_sub_one_left {a b : ℕ} (h : a - 1 ≤ b) :
insert (a - 1) (Finset.Icc a b) = Finset.Icc (a - 1) b := by
  ext x
  simp only [Finset.mem_insert, Finset.mem_Icc]
  omega

theorem Robo.ZZ.Finset.insert_Icc_eq_Icc_sub_one_left {a b : ℤ} (h : a - 1 ≤ b) :
insert (a - 1) (Finset.Icc a b) = Finset.Icc (a - 1) b := by
  ext x
  simp only [Finset.mem_insert, Finset.mem_Icc]
  omega

theorem Robo.NN.Finset.insert_Icc_add_one_left_eq_Icc {a b : ℕ} (h : a ≤ b) :
insert a (Finset.Icc (a + 1) b) = Finset.Icc a b := by
  ext x
  simp only [Finset.mem_insert, Finset.mem_Icc]
  omega

theorem Robo.ZZ.Finset.insert_Icc_add_one_left_eq_Icc {a b : ℤ} (h : a ≤ b) :
insert a (Finset.Icc (a + 1) b) = Finset.Icc a b := by
  ext x
  simp only [Finset.mem_insert, Finset.mem_Icc]
  omega

theorem Robo.NN.Finset.insert_Icc_sub_one_right_eq_Icc {a b : ℕ} (h : a ≤ b) :
insert b (Finset.Icc a (b - 1)) = Finset.Icc a b := by
  ext x
  simp only [Finset.mem_insert, Finset.mem_Icc]
  omega

theorem Robo.ZZ.Finset.insert_Icc_sub_one_right_eq_Icc {a b : ℕ} (h : a ≤ b) :
insert b (Finset.Icc a (b - 1)) = Finset.Icc a b := by
  ext x
  simp only [Finset.mem_insert, Finset.mem_Icc]
  omega


/- The following two lemmas are ℕ-versions of the previous ones, which are also already included in newer versions of mathlib:
   https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Interval/Finset/Nat.html#Nat.Icc_insert_succ_left
   https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Interval/Finset/Nat.html#Nat.Icc_insert_succ_right
   But we prefer to have just one lemma that applies to both ℕ and ℤ, so these more specific versions are not so useful.
-/
/-
theorem Nat.Icc_insert_succ_left {a b : ℕ} (h : a ≤ b) :
  insert a (Finset.Icc (a + 1) b) = Finset.Icc a b := by
  ext
  simp only [Finset.mem_insert, Finset.mem_Icc]
  omega

-- already in mathlib
--
theorem Nat.Icc_insert_succ_right {a b : ℕ} (h : a ≤ b + 1) :
insert (b + 1) (Finset.Icc a b) = Finset.Icc a (b + 1) := by
  ext x
  simp only [Finset.mem_insert, Finset.mem_Icc]
  omega
-/
