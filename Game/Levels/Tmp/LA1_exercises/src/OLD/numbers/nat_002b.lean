import numbers.nat_002

lemma add_assoc (a b c : ℕ) : a + b + c = a + (b + c) := nat.add_assoc a b c
lemma mul_assoc (a b c : ℕ) : a * b * c = a * (b * c) := nat.mul_assoc a b c
lemma add_comm (a b : ℕ) : a + b = b + a := nat.add_comm a b
lemma mul_comm (a b : ℕ) : a * b = b * a := nat.mul_comm a b

lemma add_mul (a b c: ℕ) : (a + b) * c = a * c + b * c :=
begin
  induction c with c hc,
  repeat {rw mul_zero},
  rw [nat.mul_succ, nat.mul_succ, nat.mul_succ],
  rw hc,
  repeat {rw add_assoc},
  rw ←add_assoc (b * c),
  rw add_comm (b * c) a,
  rw add_assoc,
end

lemma mul_add (a b c: ℕ) : a * (b + c) = a * b + a * c :=
begin
  repeat {rw mul_comm a},
  rw add_mul,
end
