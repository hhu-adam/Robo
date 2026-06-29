

/- L01_SMulEBasis -/
lemma Matrix.smul_ebasis {n : ℕ} (A : Mat[n,n][ℝ]) (i j) :
    A i j • E i j = single i j (A i j) := by
  unfold E
  simp


/- L02_EBasis -/
lemma Matrix.E.mul_of_ne {n : ℕ} (i j : Fin n) {k l : Fin n} (h : j ≠ k) : E i j * E k l = 0 := by
  unfold E
  simp [h]


/- L03 -/
lemma Matrix.E.mul_same {n : ℕ} (i j k : Fin n) : E i j * E j k = E i k  := by
  unfold E
  simp


/- L04_MatrixEqSum -/
lemma Matrix.matrix_eq_sum_ebasis {n : ℕ} (A : Mat[n,n][ℝ]) :
    A = ∑ i : Fin n, ∑ j : Fin n, (A i j) • E i j := by
  Branch
    unfold E
    simp
  simp [smul_ebasis] -- Lvl 1
  apply matrix_eq_sum_single


/- L05_EBasisDiagSum -/
lemma Matrix.ebasis_diag_sum_eq_one {n : ℕ} : ∑ i : Fin n, E i i = 1 := by
  Branch
    rw [matrix_eq_sum_single 1]
  rw [matrix_eq_sum_ebasis 1] -- Lvl 3
  apply sum_congr
  rfl
  intro i hi
  funext r s
  have h : {i} ⊆ univ
  · simp
  rw [← sum_subset h]
  · simp
  · intro x h₁ h₂
    clear h₁ -- not needed
    Branch
      have h₃ : x ≠ i
    have h₃ : i ≠ x
    · simp at h₂
      symm
      assumption
    Branch
      simp [h₃]
    rw [Matrix.one_apply]
    rw [if_neg h₃]
    simp


/- L06_EBasisEqOnDiag -/
lemma Matrix.eq_on_diag_ebasis {n : ℕ} {f : Mat[n,n][ℝ] →ₗ[ℝ] ℝ}
    (h₁ : ∀ A B, f (A * B) = f (B * A))  :
    ∀ (i j : Fin n), f (E i i) = f (E j j) := by
  intro i j
  Branch
    trans f (E i j * E j i)
    · unfold E
      simp
    · rw [h₁]
      unfold E
      simp
  specialize h₁ (E i j) (E j i)
  simp [E.mul_same] at h₁
  assumption


/- L07_EBasisZeroOffDiag -/
lemma Matrix.zero_on_offDiag_ebasis {n : ℕ} {f : Mat[n,n][ℝ] →ₗ[ℝ] ℝ}
    (h₁ : ∀ A B, f (A * B) = f (B * A)) :
    ∀ (i j : Fin n ), (i ≠ j) → f (E i j) = 0 := by
  intro i j hne
  Branch
    rw [← E.mul_same i j j]
    rw [h₁]
    rw [E.mul_of_ne] -- (***)
  Branch
    trans f (E i j * E j j)
    · simp [E]
    · Branch
        rw [E.mul_of_ne] -- (***)
        simp
      rw [h₁]
      rw [E.mul_of_ne] -- Lvl 2
      · simp
      · symm
        assumption
  specialize h₁ (E i j) (E j j)
  simp [E.mul_same] at h₁
  simp [E.mul_of_ne _ _ hne.symm] at h₁
  assumption


/- L08_EvalOnEBasis -/
lemma Matrix.eq_sum_apply_diag_ebasis {n : ℕ} {f : Mat[n,n][ℝ] →ₗ[ℝ] ℝ}
    (h₁ : ∀ A B, f (A * B) = f (B * A))
    (A : Mat[n,n][ℝ]) :
    f A = ∑ i : Fin n, (A i i) * f (E i i) := by
  Branch
      rw [matrix_eq_sum_ebasis A]
  nth_rw 1 [matrix_eq_sum_ebasis A] -- Lvl 3
  Branch
    simp
  rw [map_sum] -- simp knows this
  simp
  trans ∑ i, ∑ j, if i = j then (A i j) * f (E i j) else 0
  · apply congr_arg
    ext i
    apply congr_arg
    ext j
    by_cases h₂ : i = j
    · rw [if_pos h₂]
    · rw [if_neg h₂]
      rw [zero_on_offDiag_ebasis]
      · simp
      · assumption
      · assumption
  · simp


/- L09_EvalOnEBasis -/
lemma Matrix.one_on_diag_ebasis {n : ℕ} {f : Mat[n, n][ℝ] →ₗ[ℝ] ℝ}
    (h₁ : ∀ A B, f (A * B) = f (B * A)) (h₂ : f 1 = n) :
    ∀ i, f (E i i) = 1 := by
  intro i
  suffices h : n * f (E i i) = n * 1 by
    rw [mul_eq_mul_left_iff] at h
    obtain h | h := h
    · assumption
    · simp at h
      simp [h] at i
      Branch
        apply IsEmpty.false at i
        contradiction
      by_contra
      apply IsEmpty.false i
  Branch
    rw [←smul_eq_mul, ← LinearMap.map_smul]
    trans f (∑ x : Fin n, E i i)
    · simp [E] -- TODO: This is a bit magical in the sense that `simp; unfold E; simp` seems not to work
    -- · Hint (hidden := true )"**Du**: Als nächstes ziehen wir die Funktion in die Summe rein."
    · 
      trans f (∑ x, E x x)
      · Branch
          apply congr_arg
          -- Hint "**Du**: Nein, das ist jetzt mathematisch falsch!"
        rw [map_sum]
        -- Hint "**Du**: Nochmals!"
        rw [map_sum]
        apply congr_arg
        ext j
        -- Hint "**Du**: Und das war ein Resultat, welches wir auf dem Weg gefunden haben."
        -- Hint (hidden := true) "**Robo**: `eq_on_diag_ebasis` sagt meine Speicherplatte."
        rw [eq_on_diag_ebasis] -- Lvl 5
        assumption
      -- · Hint (hidden := true) "**Robo**: Das sieht nach `ebasis_diag_sum_eq_one` aus."
      · rw [ebasis_diag_sum_eq_one] -- Lvl 4
        rw [h₂]
        simp
  · trans ∑ j : Fin n, f (E i i)
    · simp
    · trans ∑ j : Fin n, f (E j j )
      · apply congr_arg
        ext
        -- Hint (hidden := true) "**Robo**: Das hatten wir schon gesehen."
        rw [eq_on_diag_ebasis] -- Lvl 5
        assumption
      · trans f 1
        -- · Hint (hidden := true) "**Robo**: Das Resultat, das du hier anwenden wolltest, hieß `eq_sum_apply_diag_ebasis`."
        · rw [eq_sum_apply_diag_ebasis] -- Lvl 8
          · simp
          · assumption
        -- · Hint (hidden := true) "**Robo**: Probier mal `rw [{h₂}]`."
        · rw [h₂]
          simp
  -- · simp -- previously needed for `nat_mul_inj'`


/- L10_Characterize -/
lemma Matrix.trace_eq {n : ℕ} (f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ)
    (h₁ : ∀ A B, f (A * B) = f (B * A)) (h₂ : f 1 = n) :
    trace = f := by
  ext A
  rw [eq_sum_apply_diag_ebasis] -- Lvl 8
  simp [one_on_diag_ebasis h₁ h₂] -- Lvl 9
  rfl
  assumption


/- L11_Linearity -/
lemma {n : ℕ} {t : ℝ} (A : Matrix (Fin n) (Fin n) ℝ) :
    trace (A - t • 1) = trace A - t • n := by
  rw [trace_sub]
  rw [trace_smul]
  rw [trace_one]
  rw [card_fin]
