import data.int.basic
import tactic.fin_cases
import data.zmod.basic
import abgaben.eduart_ort.lemmas
/-
1) Proof that no successor of a square number is divisible by three
    - implemented in sq_mod_3_succ_not_mod_3 (DONE)
2) Proof: (a % 3 ) != 0 ⇒ (a² mod 3) = 1
    - implemented in sq_mod_3_eq_1 (DONE)
3) Proof: (a % 4 ) != 0 ⇒ (a² mod 4) = 1 ∨ (a² mod 4) = 0
    - implemented in sq_mod_4_eq_1_or_0 (DONE)
4) Proof: (a % 5 ) != 0 ⇒ (a² mod 5) = 1 ∨ (a² mod 5) = 4
    - implemented in sq_mod_5_eq_1_or_4 (DONE)
5) Proof: a² + b² = c² ⇒ (a mod 3 = 0) ∨ (b mod 3 = 0)
    - implemented in pyth_triple_div_3 (DONE)
6) Proof: a² + b² = c² ⇒ (a mod 4 = 0) ∨ (b mod 4 = 0)
    - NOT IMPLEMENTED
7) Proof: a² + b² = c² ⇒ (a mod 5 = 0) ∨ (b mod 5 = 0)
    - NOT IMPLEMENTED
8) Proof: Pythagorean Triple
    - implemented in pyth_triple (DONE)
9) Proof that gcd(a, n) | c → a * x ≡ c (mod n)
    - implemented in gcd_equiv (DONE)
-/

/-
1) Proof that no successor of a square number is divisible by three
-/
theorem sq_mod_3_succ_not_mod_3 (a : ℕ) : a^2 % 3 + 1 ≠ 0 :=
begin
    by_contra h,
    generalize' ha₁ : (a : zmod 3) = a₁,
    fin_cases a₁,
    norm_cast at ha₁,
    norm_cast at ha₁,
    norm_cast at ha₁,
end

/-
2) Proof: (a % 3 ) != 0 ⇒ (a² mod 3) = 1
-/
theorem sq_mod_3_eq_1 {a : ℕ} (h : 0 ≠ a % 3) : 1 = a^2 % 3 :=
begin
    generalize' k : (a : zmod 3) = a₁,
    fin_cases a₁,
    {   -- a % 3 = 0
        change ¬ (0 ≡ a [MOD 3]) at h,
        rw [←zmod.eq_iff_modeq_nat, k] at h,
        contradiction,
    },
    {   -- a % 3 = 1
        apply sq_mod_3_of_1_eq_1,
        change  (1 ≡ a [MOD 3]),
        rw [←zmod.eq_iff_modeq_nat, k],
        ring,
    },
    {   -- a % 3 = 2
        apply sq_mod_3_of_2_eq_1,
        change  (2 ≡ a [MOD 3]),
        rw [←zmod.eq_iff_modeq_nat, k],
        ring,
    },
end


/- Proof 3: (a % 4 ) != 0 ⇒ (a² mod 4) = 1 ∨ (a² mod 4) = 0-/
theorem sq_mod_4_eq_1_or_0 {a : ℕ} (h : 0 ≠  a % 4) :
                        1 = a^2 % 4 ∨ 0 = a^2 % 4 :=
begin
    generalize' k : (a : zmod 4) = a₁,
    fin_cases a₁,
    {   -- a % 4 = 0
        change ¬ (0 ≡ a [MOD 4]) at h,
        rw [←zmod.eq_iff_modeq_nat, k] at h,
        contradiction,
    },
    {   -- a % 4 = 1
        left,
        apply sq_mod_4_of_1_eq_1,
        change  (1 ≡ a [MOD 4]),
        rw [←zmod.eq_iff_modeq_nat, k],
        ring,
    },
    {   -- a % 4 = 2
        right,
        apply sq_mod_4_of_2_eq_0,
        change  (2 ≡ a [MOD 4]),
        rw [←zmod.eq_iff_modeq_nat, k],
        ring,
    },
    {   -- a % 3 = 3
        left,
        apply sq_mod_4_of_3_eq_1,
        change  (3 ≡ a [MOD 4]),
        rw [←zmod.eq_iff_modeq_nat, k],
        ring,
    },
end

/- Proof 4: (a % 5 ) != 0 ⇒ (a² mod 5) = 1 ∨ (a² mod 5) = 4-/
theorem sq_mod_5_eq_1_or_4 {a : ℕ} (h : 0 ≠  a % 5) :
                        1 = a^2 % 5 ∨ 4 = a^2 % 5 :=
begin
    generalize' k : (a : zmod 5) = a₁,
    fin_cases a₁,
    {   -- a % 5 = 0
        change ¬ (0 ≡ a [MOD 5]) at h,
        rw [←zmod.eq_iff_modeq_nat, k] at h,
        contradiction,
    },
    {   -- a % 5 = 1
        left,
        apply sq_mod_5_of_1_eq_1,
        change  (1 ≡ a [MOD 5]),
        rw [←zmod.eq_iff_modeq_nat, k],
        ring,
    },
    {   -- a % 5 = 2
        right,
        apply sq_mod_5_of_2_eq_4,
        change  (2 ≡ a [MOD 5]),
        rw [←zmod.eq_iff_modeq_nat, k],
        ring,
    },
    {   -- a % 5 = 3
        right,
        apply sq_mod_5_of_3_eq_4,
        change  (3 ≡ a [MOD 5]),
        rw [←zmod.eq_iff_modeq_nat, k],
        ring,
    },
    {   -- a % 5 = 4
        left,
        apply sq_mod_5_of_4_eq_1,
        change  (4 ≡ a [MOD 5]),
        rw [←zmod.eq_iff_modeq_nat, k],
        ring,
    },
end

/-
Proof 5:  a² + b² = c² ⇒ (a mod 3 = 0) ∨ (b mod 3 = 0)
-/
theorem pyth_triple_div_3 ( a b c : ℕ) :  ((a ^ 2) % 3 + (b ^ 2) % 3) % 3  = (c ^ 2) % 3 → 0 = a % 3 ∨ 0 = b % 3 :=
begin
    intro h,
    by_contra k,
    rw not_or_distrib at k,
    rcases k,
    generalize' ha₁ : (a : zmod 3) = a₁,
    generalize' hb₁ : (b : zmod 3) = b₁,
    fin_cases a₁,
    {
        fin_cases b₁,
        {   -- cases where assumptions are not met
            change ¬ (0 ≡ a [MOD 3]) at k_left,
            rw [←zmod.eq_iff_modeq_nat, ha₁] at k_left,
            contradiction,
        },
        {   -- cases where assumptions are not met
            change ¬ (0 ≡ a [MOD 3]) at k_left,
            rw [←zmod.eq_iff_modeq_nat, ha₁] at k_left,
            contradiction,
        },
        {   -- cases where assumptions are not met
            change ¬ (0 ≡ a [MOD 3]) at k_left,
            rw [←zmod.eq_iff_modeq_nat, ha₁] at k_left,
            contradiction,
        },
    },
    {
        fin_cases b₁,
        {   -- cases where assumptions are not met
            change ¬ (0 ≡ b [MOD 3]) at k_right,
            rw [←zmod.eq_iff_modeq_nat, hb₁] at k_right,
            contradiction,
        },
        {   -- case: a = 1, b=1
            suffices h_a : 1 = a ^ 2 % 3,
            suffices h_b : 1 = b ^ 2 % 3,
            -- replace values
            rw [←h_a, ← h_b] at h,
            apply sq_mod_3_uneq_2,
            assumption,
            -- proof the suffices
            {
                apply mod_3_eq1_for_1,
                assumption,
            },
            {
                apply mod_3_eq1_for_1,
                assumption,
            },
        },
        {   -- case: a = 1, b=2
            suffices h_a : 1 = a ^ 2 % 3,
            suffices h_b : 1 = b ^ 2 % 3,
            -- replace values
            rw [←h_a, ← h_b] at h,
            apply sq_mod_3_uneq_2,
            assumption,
            -- proof the suffices
            {
                apply mod_3_eq2_for_1,
                assumption,
            },
            {
                apply mod_3_eq1_for_1,
                assumption,
            },
        },
    },
    {
        fin_cases b₁,
        {   -- cases where assumptions are not met
            change ¬ (0 ≡ b [MOD 3]) at k_right,
            rw [←zmod.eq_iff_modeq_nat, hb₁] at k_right,
            contradiction,
        },
        {   -- case: a = 2, b=1
            suffices h_a : 1 = a ^ 2 % 3,
            suffices h_b : 1 = b ^ 2 % 3,
            -- replace values
            rw [←h_a, ← h_b] at h,
            apply sq_mod_3_uneq_2,
            assumption,
            -- proof the suffices
            {
                apply mod_3_eq1_for_1,
                assumption,
            },
            {
                apply mod_3_eq2_for_1,
                assumption,
            },
        },
        {   -- case: a = 2, b=2
            suffices h_a : 1 = a ^ 2 % 3,
            suffices h_b : 1 = b ^ 2 % 3,
            -- replace values
            rw [←h_a, ← h_b] at h,
            apply sq_mod_3_uneq_2,
            assumption,
            -- proof the suffices
            {
                apply mod_3_eq2_for_1,
                assumption,
            },
            {
                apply mod_3_eq2_for_1,
                assumption,
            },
        },
    },
end

/-
Proof 6:  a² + b² = c² ⇒ (a mod 4 = 0) ∨ (b mod 4 = 0)
-/
theorem pyth_triple_div_4( a b c : ℕ) :  a ^ 2 % 4 + b ^ 2 % 4  = c ^ 2 % 4 → 0 = a % 4 ∨ 0 = b % 4 ∨ 0 = c % 4 :=
begin
    sorry
end

/-
Proof 7:  a² + b² = c² ⇒ (a mod 5 = 0) ∨ (b mod 5 = 0) ∨ (c mod 5 = 0)
-/
theorem pyth_triple_div_5( a b c : ℕ) :  a ^ 2 % 5 + b ^ 2 % 5  = c ^ 2 % 5 → 0 = a % 5 ∨ 0 = b % 5 ∨ 0 = c % 5 :=
begin
    sorry,
end

/-
Proof 8:  Pythagorean triple
-/
theorem pyth_triple {m n a b c : ℤ}(ha : a = m ^ 2 - n ^ 2)(hb : b = 2 * m * n) (hc : c = m ^ 2 + n ^ 2): a^2 + b^2 = c^2 :=
begin
    -- substitute
    rw [ha, hb, hc ] at *,
    -- et voila
    ring,
end

/-
Proof 9:   gcd(a, n) | c → a * x ≡ c (mod n)
-/
theorem gcd_equiv (a b n : ℤ) ( c : ℕ): (int.gcd a n ∣ c)  → ∃ x, a * x ≡ c [ZMOD n]:=
begin
    intro h₁,
    rcases h₁ with ⟨k, hk⟩,
    let x := a.gcd_a n,
    have bez := int.gcd_eq_gcd_ab a n, -- Bezout's Lemma
    rw hk,
    simp,
    rw bez,
    use a.gcd_a n * k,
    rw int.modeq_iff_dvd,
    ring_nf,
    simp,
end