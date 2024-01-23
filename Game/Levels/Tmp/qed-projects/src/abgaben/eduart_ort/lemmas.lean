import data.int.basic
import tactic.fin_cases
import data.zmod.basic

lemma sq_mod_3_of_0_eq_0 {a : ℕ} (h : 0 = a % 3) : 0 = a^2 % 3 :=
begin
    rw [pow_two, nat.mul_mod a a 3, ←h],
    ring,
end 

lemma sq_mod_3_of_1_eq_1 {a : ℕ} (h : 1 = a % 3) : 1 = a^2 % 3 :=
begin
    rw [pow_two, nat.mul_mod a a 3, ←h],
    ring,
end 

lemma sq_mod_3_of_2_eq_1 {a : ℕ} (h : 2 = a % 3) : 1 = a^2 % 3 :=
begin
    rw [pow_two, nat.mul_mod a a 3, ←h],
    ring,
end 

lemma sq_mod_4_of_1_eq_1 {a : ℕ} (h : 1 = a % 4) : 1 = a^2 % 4 :=
begin
    rw [pow_two, nat.mul_mod a a 4, ←h],
    ring,
end 

lemma sq_mod_4_of_2_eq_0 {a : ℕ} (h : 2 = a % 4) : 0 = a^2 % 4:=
begin
    rw [pow_two, nat.mul_mod a a 4, ←h],
    ring,
end 

lemma sq_mod_4_of_3_eq_1 {a : ℕ} (h : 3 = a % 4) : 1 = a^2 % 4 :=
begin
    rw [pow_two, nat.mul_mod a a 4, ←h],
    ring,
end 
lemma sq_mod_5_of_1_eq_1 {a : ℕ} (h : 1 = a % 5) : 1 = a^2 % 5 :=
begin
    rw [pow_two, nat.mul_mod a a 5, ←h],
    ring,
end 

lemma sq_mod_5_of_2_eq_4 {a : ℕ} (h : 2 = a % 5) : 4 = a^2 % 5:=
begin
    rw [pow_two, nat.mul_mod a a 5, ←h],
    ring,
end 

lemma sq_mod_5_of_3_eq_4 {a : ℕ} (h : 3 = a % 5) : 4 = a^2 % 5 :=
begin
    rw [pow_two, nat.mul_mod a a 5, ←h],
    ring,
end 

lemma sq_mod_5_of_4_eq_1 {a : ℕ} (h : 4 = a % 5) : 1 = a^2 % 5 :=
begin
    rw [pow_two, nat.mul_mod a a 5, ←h],
    ring,
end 

lemma mod_3_eq1_for_1 {a : ℕ} (ha : (a : zmod 3) = 1):
                        1 = a ^ 2 % 3 :=
begin
    apply sq_mod_3_of_1_eq_1, 
    change (1 ≡ a [MOD 3]),
    rw ←zmod.eq_iff_modeq_nat,
    tauto,
end
lemma mod_3_eq2_for_1 {a : ℕ} (ha : (a : zmod 3) = 2):
                        1 = a ^ 2 % 3 :=
begin
    apply sq_mod_3_of_2_eq_1, 
    change (2 ≡ a [MOD 3]),
    rw ←zmod.eq_iff_modeq_nat,
    tauto,
end

lemma split_mod_eq (a : ℕ) : 2 ≠ a % 3 ↔ 0 = a % 3 ∨ 1 = a % 3  :=
begin
  constructor,
  { -- Direction: → 
    intro h,
    change  (0 ≡ a [MOD 3]) ∨ (1 ≡ a [MOD 3]),
    change ¬ (2 ≡ a [MOD 3]) at h,
    simp_rw [←zmod.eq_iff_modeq_nat 3] at *,
    generalize' k : (a : zmod 3) = a₁,
    fin_cases a₁,
    tauto,
    tauto,
    tauto,
  },
  { 
    -- Direction: ← 
    intro h,
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
