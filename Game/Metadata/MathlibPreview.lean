import Game.Metadata.FromMathlib

-- mathlib PR: ………
theorem Set.subset_iff {A : Type} {s₁ s₂ : Set A} : s₁ ⊆ s₂ ↔ ∀ {x : A}, x ∈ s₁ → x ∈ s₂ := by
  rfl

-- mathlib PR: #19255
alias _root_.Nat.prime_def := Nat.prime_def_lt''


/-- Icc_insert lemmas
    - for ℤ, need very general version Finset.insert_Icc_ …
      One exercise in Babylon will use this!
    - for ℕ, there's a dedicated version Nat.Icc_insert …, which I current
      This is the version currently proved in Luna.
--/


-- alread in mathlib
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Order/Interval/Finset/SuccPred.html#Finset.insert_Icc_add_one_left_eq_Icc
theorem Finset.insert_Icc_eq_Icc_add_one_right {a b : ℕ} (h : a ≤ b + 1) :
  insert (b + 1) (Icc a b) = Icc a (b + 1) := by
  ext x
  simp only [mem_insert, mem_Icc]
  omega

-- already in mathlib
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Interval/Finset/Nat.html#Nat.Icc_insert_succ_right
theorem Nat.Icc_insert_succ_right {a b : ℕ} (h : a ≤ b + 1) :
insert (b + 1) (Finset.Icc a b) = Finset.Icc a (b + 1) := by
  ext x
  simp only [Finset.mem_insert, Finset.mem_Icc]
  omega

-- already in mathlib, in much more general form
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Order/Interval/Finset/SuccPred.html#Finset.insert_Icc_add_one_left_eq_Icc
theorem Finset.insert_Icc_add_one_left_eq_Icc {a b : ℕ} (h : a ≤ b) :
insert a (Icc (a + 1) b) = Icc a b := by
  ext x
  simp only [mem_insert, mem_Icc]
  omega

-- already in mathlib
-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Interval/Finset/Nat.html#Nat.Icc_insert_succ_left
theorem Nat.Icc_insert_succ_left {a b : ℕ} (h : a ≤ b) :
  insert a (Finset.Icc (a + 1) b) = Finset.Icc a b := by
  ext
  simp only [Finset.mem_insert, Finset.mem_Icc]
  omega
