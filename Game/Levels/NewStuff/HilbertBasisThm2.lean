import Game.Metadata

/-! This follows the proof in mathlib. -/

-- variables  [DecidableEq R] [DecidableEq R[X]]

set_option autoImplicit false

open Polynomial

#check Polynomial.isNoetherianRing

theorem Polynomial.isNoetherianRing' {R : Type*} [CommRing R]
    [R_noetherian : IsNoetherianRing R] : IsNoetherianRing R[X] := by
  rw [isNoetherianRing_iff_ideal_fg]
  intro I

  let S : Set <| Ideal R := {I.leadingCoeffNth n | n : ℕ}
  have S_notempty : Set.Nonempty S := by
    exact ⟨_, ⟨0, rfl⟩⟩

  have X₁ : IsNoetherian R R := by infer_instance
  rw [isNoetherian_iff_wellFounded] at X₁

  let M : Ideal R := WellFounded.min X₁ S S_notempty
  have hm : M ∈ S := WellFounded.min_mem X₁ S S_notempty
  rcases hm with ⟨N, HN⟩

  rcases I.is_fg_degreeLE N with ⟨s, hs⟩

  have hm2 : ∀ k, I.leadingCoeffNth k ≤ M := by
    intro k

    exact Or.casesOn (le_or_lt k N) (fun h => HN ▸ I.leadingCoeffNth_mono h) fun h x hx =>
      Classical.by_contradiction fun hxm =>
        haveI : IsNoetherian R R := R_noetherian
        have : ¬M < I.leadingCoeffNth k := by
          refine' WellFounded.not_lt_min (wellFounded_submodule_gt R R) _ _ _; exact ⟨k, rfl⟩
        this ⟨HN ▸ I.leadingCoeffNth_mono (le_of_lt h), fun H => hxm (H hx)⟩

  have hs2 : ∀ {x}, x ∈ I.degreeLE N → x ∈ Ideal.span (↑s : Set R[X]) :=
    hs ▸ fun hx =>
      Submodule.span_induction hx (fun _ hx => Ideal.subset_span hx) (Ideal.zero_mem _)
        (fun _ _ => Ideal.add_mem _) fun c f hf => f.C_mul' c ▸ Ideal.mul_mem_left _ _ hf

  use s
  apply le_antisymm
  apply Ideal.span_le.2
  intro x hx
  have : x ∈ I.degreeLE N := hs ▸ Submodule.subset_span hx
  exact this.2
  have xy : Submodule.span R[X] ↑s = Ideal.span ↑s := rfl
  rw [← xy]
  intro p hp
  generalize hn : p.natDegree = k
  induction' k using Nat.strong_induction_on with k ih generalizing p
  rcases le_or_lt k N with h | h
  · subst k
    refine' hs2 ⟨Polynomial.mem_degreeLE.2
      (le_trans Polynomial.degree_le_natDegree <| WithBot.coe_le_coe.2 h), hp⟩
  · have hp0 : p ≠ 0 := by
      rintro rfl
      cases hn
      exact Nat.not_lt_zero _ h
    have : (0 : R) ≠ 1 := by
      intro h
      apply hp0
      ext i
      refine' (mul_one _).symm.trans _
      rw [← h, mul_zero]
      rfl
    haveI : Nontrivial R := ⟨⟨0, 1, this⟩⟩
    have : p.leadingCoeff ∈ I.leadingCoeffNth N := by
      rw [HN]
      exact hm2 k ((I.mem_leadingCoeffNth _ _).2
        ⟨_, hp, hn ▸ Polynomial.degree_le_natDegree, rfl⟩)
    rw [I.mem_leadingCoeffNth] at this
    rcases this with ⟨q, hq, hdq, hlqp⟩
    have hq0 : q ≠ 0 := by
      intro H
      rw [← Polynomial.leadingCoeff_eq_zero] at H
      rw [hlqp, Polynomial.leadingCoeff_eq_zero] at H
      exact hp0 H
    have h1 : p.degree = (q * Polynomial.X ^ (k - q.natDegree)).degree := by
      rw [Polynomial.degree_mul', Polynomial.degree_X_pow]
      rw [Polynomial.degree_eq_natDegree hp0, Polynomial.degree_eq_natDegree hq0]
      rw [← Nat.cast_add, add_tsub_cancel_of_le, hn]
      · refine' le_trans (Polynomial.natDegree_le_of_degree_le hdq) (le_of_lt h)
      rw [Polynomial.leadingCoeff_X_pow, mul_one]
      exact mt Polynomial.leadingCoeff_eq_zero.1 hq0
    have h2 : p.leadingCoeff = (q * Polynomial.X ^ (k - q.natDegree)).leadingCoeff := by
      rw [← hlqp, Polynomial.leadingCoeff_mul_X_pow]
    have := Polynomial.degree_sub_lt h1 hp0 h2
    rw [Polynomial.degree_eq_natDegree hp0] at this
    rw [← sub_add_cancel p (q * Polynomial.X ^ (k - q.natDegree))]
    refine' (Ideal.span ↑s).add_mem _ ((Ideal.span ↑s).mul_mem_right _ _)
    · by_cases hpq : p - q * Polynomial.X ^ (k - q.natDegree) = 0
      · rw [hpq]
        exact Ideal.zero_mem _
      refine' ih _ _ (I.sub_mem hp (I.mul_mem_right _ hq)) rfl
      rwa [Polynomial.degree_eq_natDegree hpq, Nat.cast_lt, hn] at this
    exact hs2 ⟨Polynomial.mem_degreeLE.2 hdq, hq⟩
