import data.int.basic
import data.int.gcd
import data.int.modeq
import data.nat.modeq
import tactic.fin_cases
import data.zmod.basic
import data.fin.basic
import algebra.group_power.lemmas

-- part 1
-- Wenn c % gcd(a,n) = 0 -> a * x equiv c mod n
theorem euclid_algorithm (a c n x : ℕ  ) : ( nat.gcd a n ) ∣ c → a * x ≡ c [MOD n]
:=
begin
    intro h,
    sorry,
end

-- part 2
-- namespace nat
-- lemma gcdCompExample (a b : ℕ )  {h : a = 73} {k : b = 55}: gcd a b = 1 :=
-- begin
--     rw h,
--     rw k,
--     unfold gcd,
--     --refl,
--     sorry,
-- end
--  end nat
-- #eval nat.gcd 73 55

-- 4
lemma sq_mod_4_of_2_eq_withMOD (a : ℕ) {h : 2 = a % 4} : 0 = a^2 % 4:=
begin
    rw pow_succ,
    simp,
    rw nat.mul_mod a a 4,
    rw [← h],
    ring,
end

-- Lemma formuliert als Equivalenzklassen:
lemma xy1 {a : zmod 4} (h : 2 = a) : 0 = a^2 :=
begin
    rw [← h],
    ring,
end

lemma xy2 {a : ℕ} (h : 2 = a % 4) : 0 = a^2 % 4:=
begin
  change 0 ≡ a ^ 2 [MOD 4],
  change 2 ≡ a [MOD 4] at h,
  simp_rw [←zmod.eq_iff_modeq_nat] at *,
  norm_num,
  apply xy1,
  exact h,
end

lemma sq_mod_4_of_2_eq_0_withEQ (a : ℕ) {h : 2 ≡ a [MOD 4]} : 0 ≡ a^2 [MOD 4] :=
begin
    change (2 = a % 4) at h,
    change  (0 = a^2 % 4),
    apply sq_mod_4_of_2_eq_withMOD,
    assumption,
    -- rw ← zmod.eq_iff_modeq_nat at *,
    -- rw pow_succ,
    -- simp,
    -- rw [← h],
    -- tauto,
end



-- 4
lemma sq_mod_4_of_3_eq_1 (a : ℕ) {h  : 3 = a % 4} :
    1 = a^2 % 4 :=
begin
    rw pow_succ,
    simp,
    rw [nat.mul_mod a a 4, ←h],
    ring,
end

lemma sq_mod_4_of_1_eq_1 (a : ℕ) {h : 1 = a % 4} :
    1 = a^2 % 4 :=
begin
    rw pow_succ,
    simp,
    rw [nat.mul_mod a a 4, ←h],
    ring,
end


lemma sq_mod_4_eq_1_or_0 (a : ℕ) {h : 1 = a % 4 ∨ 2 = a % 4 ∨ 3 = a % 4 } :
                        1 = a^2 % 4 ∨ 0 = a^2 % 4 :=
begin
    rcases h with h | h,
    left,
    apply sq_mod_4_of_1_eq_1,
    assumption,
    rcases h with h | h,
    right,
    apply sq_mod_4_of_2_eq_withMOD,
    assumption,
    left,
    apply sq_mod_4_of_3_eq_1,
    assumption
end

lemma sq_mod_4_eq_1_or_0_2 (a : ℕ   ) {h :  ¬( 0 ≡ a [MOD 4])} :
                        a^2 % 4 = 1 ∨ a^2 % 4 = 0 :=
begin
    generalize' k : (a : zmod 4) = a₁,
    fin_cases a₁,
    {
        rw ← zmod.eq_iff_modeq_nat at h,
        rw k at h,
        contradiction,
    },
    {
        left,
        rw sq_mod_4_of_1_eq_1,
        rw k at *,
    },
    {
        right,
        rw sq_mod_4_of_2_eq_0,
        sorry,
    },
    {
        left,
        rw sq_mod_4_of_3_eq_1,
        sorry,
    },
end



-- this lemma should replace the next one, but needs some
-- more fixing. Goal is to translate a negation into its
-- cases
lemma sq_mod_3_eq_1_2 (a : ℕ) {h : a % 3 ≠ 0} :
                        a^2 % 3 = 1 :=
begin
    --change (a ≡ 1 [MOD 3]) at h,
    generalize' ha₁ : (a : zmod 3) = a₁,
    fin_cases a₁,
    rw ha₁ at h,

    --rw ← sub_zero at h,
    --rw ← int.int.modeq.dvd at h,
    --apply not_div_3_eq_1_2
    --rcases h with h | h,
    sorry,
end
lemma sq_mod_3_eq_1 (a : ℕ) {h : 1 = a % 3 ∨ 2 = a % 3 } :
                        a^2 % 3 = 1 :=
begin
    rcases h with h | h,
    rw pow_succ,
    simp,
    rw nat.mul_mod a a 3,
    rw [← h],
    ring,
    rw pow_succ,
    simp,
    rw nat.mul_mod a a 3,
    rw [← h],
    ring,
end

lemma not_div_3_eq_1_2_old (a : ℕ ) : ¬ (3 ∣ a )  →  a % 3 = 1 ∨ a % 3 = 2 :=
 begin
    contrapose,
    rw not_not,
    intro h,
    rw not_or_distrib at h,
    rcases h,
    change ¬ (a ≡ 1 [MOD 3]) at h_left,
    change ¬ (a ≡ 2 [MOD 3]) at h_right,
    generalize' ha₁ : (a : zmod 3) = a₁,
    rw ha₁ at *,
    fin_cases a₁,
    -- need to deal with the case a = 0,
    -- upcasting doesnt work here
    sorry,
    --norm_cast at ha₁,

        -- rw ←int.coe_nat_modeq_iff at h,
        -- rw int.modeq_iff_dvd at h,
        -- rw ← zmod.eq_iff_modeq_nat at h,
        -- rw int.coe_nat_eq at k,
    sorry,
    sorry,
end

lemma not_div_3_eq_1_2 (a : ℤ  ) : ¬ (3 ∣ a )  ↔
  a % 3 = 1 ∨ a % 3 = 2 :=
 begin
    constructor,
    sorry,
    {
        intro h,
        rcases h,
        change (a ≡ 1 [ZMOD 3]) at h,
        generalize' ha₁ : (a : zmod 3) = a₁,
        rw ha₁ at *,
        rw ← int.modeq_zero_iff_dvd,
        fin_cases a₁,
        {
            rw ←zmod.eq_iff_modeq_nat at h,
            rw ha₁ at h,
            simp at *,
            contradiction,
        },
        {
            rw ← zmod.eq_iff_modeq_nat at h,
            simp at *,
            sorry,
            --rw ← int.modeq_zero_iff_dvd 3 a,
        },
        sorry,
        sorry,
    }
    -- need to deal with the case a = 0,
    -- upcasting doesnt work here

    --norm_cast at ha₁,

end

lemma sq_mod_3_succ_not_mod_3 (a : ℕ) :
                        a^2 % 3 + 1 ≠ 0 :=
begin
    by_contra h,
    generalize' ha₁ : (a : zmod 3) = a₁,
    fin_cases a₁,
    norm_cast at ha₁,
    norm_cast at ha₁,
    norm_cast at ha₁,
end

-- part 4
/- continue the proof-/
example ( a b c :  ℕ   ) :  a ^ 2  + b ^ 2 = c ^ 2 → 0 = a % 3  ∨  0 = b %  3 :=
begin
    intro h,
    by_contra k,
    rw not_or_distrib at k,
    rcases k,
    change ¬ (0 ≡ a [MOD 3]) at k_left,

    generalize' ha₁ : (a : zmod 3) = a₁,
    generalize' hb₁ : (b : zmod 3) = b₁,
    rw ha₁ at *,
    fin_cases a₁,
    fin_cases b₁,
    norm_cast at ha₁,
    norm_cast at hb₁,
    sorry,
    sorry,
    sorry,
    sorry,
    sorry,
    -- rw ← sq_mod_3_eq_1 at ha₁,
    -- rw sq_mod_3_eq_1 at hb₁,
    -- apply sqare_mod_3_eq_1,
    -- rcases k,



    -- have k :  a ^ 2 % 3 = 1,
    -- have l :  b ^ 2 % 3 = 1,

    --contradiction,
end


theorem pyth_triple (m n a b c : ℕ){ha : a = m ^ 2 - n ^ 2 }{hb : b = 2 * m * n} {hc : c = m ^ 2 + n ^ 2}: a^2 + b^2 = c^2 :=
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


-- example (n : nat) : n + 0 = n := by show_term {simp}

-- example (n : nat) : n + 0 = n := add_zero n

-- part 5
/- some more restklassenbeweise-/