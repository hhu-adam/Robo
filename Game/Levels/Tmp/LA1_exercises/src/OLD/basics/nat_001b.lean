import basics.numbers.nat_001

lemma mul_zero (a : ℕ) : a * 0 = 0 :=
begin
  refl
end

lemma zero_mul (a : ℕ) : 0 * a = 0 :=
begin
  induction a with a ha,
  refl,
  rw nat.mul_succ,
  rw ha,
end

lemma mul_one (a : ℕ) : a * 1 = a :=
begin
  rw nat.mul_succ,
  rw mul_zero,
  rw zero_add,
end

lemma one_mul (a : ℕ) : 1 * a = a :=
begin
  rw nat.succ_mul,
  rw zero_mul,
  rw zero_add,
end
