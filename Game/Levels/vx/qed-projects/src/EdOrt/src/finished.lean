import data.int.basic
import tactic.fin_cases
import data.zmod.basic
/-
Lemmas
1) Proof that no successor of a square number is divisible by three
    - implemented in sq_mod_3_succ_not_mod_3 (DONE)
2) Proof: (a % 3 ) != 0 ⇒ (a² mod 3) = 1
    - implemented in sq_mod_3_eq_1 (DONE)
3) Proof: (a % 4 ) != 0 ⇒ (a² mod 4) = 1 ∨ (a² mod 4) = 0
    - implemented in sq_mod_4_eq_1_or_0 (DONE)
4) Proof: (a % 5 ) != 0 ⇒ (a² mod 5) = 1 ∨ (a² mod 5) = 1
    - implemented in sq_mod_5_eq_1_or_4 (DONE)
5) Proof: a² + b² = c² ⇒ (a mod 3 = 0) ∨ (b mod 3 = 0)
    - WIP
6) Proof: a² + b² = c² ⇒ (a mod 4 = 0) ∨ (b mod 4 = 0)
    - WIP
7) Proof: a² + b² = c² ⇒ (a mod 5 = 0) ∨ (b mod 5 = 0)
    - WIP
8) Proof: Pythagorean Triple
    - WIP
9) Proof that gcd(a, n) | c → a * x ≡ c (mod n)
    - No time...
-/

/-
Preparatory lemmas for proof (2 and 4)
-/
lemma sq_mod_3_of_0_eq_0 (a : ℕ) {h : 0 = a % 3} : 0 = a^2 % 3 :=
begin
    rw [pow_two, nat.mul_mod a a 3, ←h],
    ring,
end

lemma sq_mod_3_of_1_eq_1 (a : ℕ) {h : 1 = a % 3} : 1 = a^2 % 3 :=
begin
    rw [pow_two, nat.mul_mod a a 3, ←h],
    ring,
end

lemma sq_mod_3_of_2_eq_1 (a : ℕ) {h : 2 = a % 3} : 1 = a^2 % 3 :=
begin
    rw [pow_two, nat.mul_mod a a 3, ←h],
    ring,
end

lemma sq_mod_4_of_1_eq_1 (a : ℕ) {h : 1 = a % 4} : 1 = a^2 % 4 :=
begin
    rw [pow_two, nat.mul_mod a a 4, ←h],
    ring,
end

lemma sq_mod_4_of_2_eq_0 (a : ℕ) {h : 2 = a % 4} : 0 = a^2 % 4:=
begin
    rw [pow_two, nat.mul_mod a a 4, ←h],
    ring,
end

lemma sq_mod_4_of_3_eq_1 (a : ℕ) {h : 3 = a % 4} : 1 = a^2 % 4 :=
begin
    rw [pow_two, nat.mul_mod a a 4, ←h],
    ring,
end
lemma sq_mod_5_of_1_eq_1 (a : ℕ) {h : 1 = a % 5} : 1 = a^2 % 5 :=
begin
    rw [pow_two, nat.mul_mod a a 5, ←h],
    ring,
end

lemma sq_mod_5_of_2_eq_4 (a : ℕ) {h : 2 = a % 5} : 4 = a^2 % 5:=
begin
    rw [pow_two, nat.mul_mod a a 5, ←h],
    ring,
end

lemma sq_mod_5_of_3_eq_4 (a : ℕ) {h : 3 = a % 5} : 4 = a^2 % 5 :=
begin
    rw [pow_two, nat.mul_mod a a 5, ←h],
    ring,
end

lemma sq_mod_5_of_4_eq_1 (a : ℕ) {h : 4 = a % 5} : 1 = a^2 % 5 :=
begin
    rw [pow_two, nat.mul_mod a a 5, ←h],
    ring,
end

/- Additional lemmas that are not entirely clear to me at the moment-/
lemma mod_3_1 (a : ℕ) {h :  (a : zmod 3) = 1} :
                        1 = a ^ 2 % 3 :=
begin
    apply sq_mod_3_of_1_eq_1,
    change (1 ≡ a [MOD 3]),
    sorry
    -- rw [←zmod.eq_iff_modeq_nat, ←h],
    -- tauto,
end
lemma mod_3_2 (a : ℕ) {h : (a : zmod 3) = 2} :
                        1 = a ^ 2 % 3 :=
begin
    sorry
    -- apply sq_mod_3_of_2_eq_1,
    -- change (2 ≡ a [MOD 3]),
    -- rw [←zmod.eq_iff_modeq_nat, ←h],
    -- tauto,
end

-- this lemma is super trivial, but I don't know how to prove it
lemma split_mod_eq (a : ℕ) : 2 ≠ a % 3 ↔  0 = a % 3 ∨ 1 = a % 3  :=
begin
  -- HERE
  constructor,
  intro h,
  { change  (0 ≡ a [MOD 3]) ∨ (1 ≡ a [MOD 3]),
    change ¬ (2 ≡ a [MOD 3]) at h,
    simp_rw [←zmod.eq_iff_modeq_nat 3] at *,
    generalize' k : (a : zmod 3) = a₁,
    fin_cases a₁,
    tauto,
    tauto,
    tauto,
  },
  { intro h,
    by_contra h₂,
    rcases h with h | h,
    {
      rw [← h] at h₂,
      contradiction,
    },
    { rw [← h₂] at h,
      -- ok this' got to be easier…
      suffices : 1 ≠ 2,
      { contradiction },
      apply nat.one_ne_bit0,
    },
  }

end

lemma sq_mod_3_uneq_2 (a : ℕ) : 2 ≠ a^2 % 3 :=
begin
    generalize' k : (a : zmod 3) = a₁,
    fin_cases a₁,
    {   -- a % 3 = 0
    rw split_mod_eq,
    left,
    apply sq_mod_3_of_0_eq_0,
        change (0 ≡ a [MOD 3]),
        rw [←zmod.eq_iff_modeq_nat, k],
        ring,
    },
    {   -- a % 3 = 1
        rw split_mod_eq,
        right,
        apply sq_mod_3_of_1_eq_1,
        change  (1 ≡ a [MOD 3]),
        rw [←zmod.eq_iff_modeq_nat, k],
        ring,
    },
    {   -- a % 3 = 2
        rw split_mod_eq,
        right,
        apply sq_mod_3_of_2_eq_1,
        change  (2 ≡ a [MOD 3]),
        rw [←zmod.eq_iff_modeq_nat, k],
        ring,
    },
end

/-
1) Proof that no successor of a square number is divisible by three
-/
lemma sq_mod_3_succ_not_mod_3 (a : ℕ) : a^2 % 3 + 1 ≠ 0 :=
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
lemma sq_mod_3_eq_1 (a : ℕ) {h : 0 ≠ a % 3} : 1 = a^2 % 3 :=
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
lemma sq_mod_4_eq_1_or_0 (a : ℕ) {h : 0 ≠  a % 4} :
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
lemma sq_mod_5_eq_1_or_4 (a : ℕ) {h : 0 ≠  a % 5} :
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


lemma tmp (b : ℕ) (hb : (b : zmod 3) = 2): 1 = b ^ 2 % 3 :=
begin
  apply sq_mod_3_of_2_eq_1,
  change (2 ≡ b [MOD 3]),
  rw [←zmod.eq_iff_modeq_nat],
  rw [hb],
  tauto,
end

example {a b c : ℕ } (h : a ^ 2 + b ^ 2 = c ^ 2) :
  (a ^ 2 % 3 + b ^ 2 % 3) % 3 = c ^ 2 % 3 :=
begin
  rw [← h],
  simp?,
  -- simp only [eq_self_iff_true, nat.add_mod_mod, nat.mod_add_mod]
end

/-
Proof 5:  a² + b² = c² ⇒ (a mod 3 = 0) ∨ (b mod 3 = 0)
-/
theorem pyth_triple_div_3( a b c : ℕ) :  (a ^ 2 % 3+ b ^ 2 % 3) % 3  = c ^ 2 % 3 → 0 = a % 3 ∨ 0 = b % 3 :=
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
        --have h_sq : 1 = a ^ 2 % 3 := by sq_mod_3_eq_1,

        {   -- case: a = 1, b=1
            suffices h_a : 1 = a ^ 2 % 3,
            suffices h_b : 1 = b ^ 2 % 3,
            -- replace values
            rw [←h_a, ← h_b] at h,
            apply sq_mod_3_uneq_2,
            assumption,
            -- proof the suffices
            {
              apply sq_mod_3_of_1_eq_1,
              change (1 ≡ b [MOD 3]),
              rw [←zmod.eq_iff_modeq_nat],
              rw [hb₁],
              tauto,
            },
            {
                apply sq_mod_3_of_1_eq_1,
                change (1 ≡ a [MOD 3]),
                rw [←zmod.eq_iff_modeq_nat, ha₁],
                tauto,
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
              apply tmp,
              assumption,
            },
            {
                apply sq_mod_3_of_1_eq_1,
                change (1 ≡ a [MOD 3]),
                rw [←zmod.eq_iff_modeq_nat, ha₁],
                tauto,
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
                -- apply mod_3_1,
                sorry,
            },
            {
                apply sq_mod_3_of_2_eq_1,
                change (2 ≡ a [MOD 3]),
                rw [←zmod.eq_iff_modeq_nat, ha₁],
                tauto,
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
                -- apply mod_3_2,
                sorry,
            },
            {
                apply sq_mod_3_of_2_eq_1,
                change (2 ≡ a [MOD 3]),
                rw [←zmod.eq_iff_modeq_nat, ha₁],
                tauto,
            },
        },
    },
end

/-
Proof 6:  a² + b² = c² ⇒ (a mod 4 = 0) ∨ (b mod 4 = 0)
-/
theorem pyth_triple_div_4( a b c : ℕ) :  a ^ 2 % 4 + b ^ 2 % 4  = c ^ 2 % 4 → 0 = a % 4 ∨ 0 = b % 4 :=
begin
    sorry,
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
theorem pyth_triple (m n a b c : ℤ){ha : a = m ^ 2 - n ^ 2 }{hb : b = 2 * m * n} {hc : c = m ^ 2 + n ^ 2}: a^2 + b^2 = c^2 :=
begin
    -- substitute
    rw [ha, hb, hc ] at *,

    -- middle term
    rw [mul_pow, mul_pow],
    ring_nf,
    -- right side
    rw [right_distrib, ←pow_add],
    ring_nf,
    -- left side
    --rw sub_pow_two at *,
    rw nat.sq_sub_sq at *,
    rw [mul_pow, add_pow_two],

    rw sub_pow_two at *,
end