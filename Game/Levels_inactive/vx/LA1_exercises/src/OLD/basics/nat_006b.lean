
import basics.numbers.nat_005
import tactic.alias

lemma succ_inj (a b : ℕ) : a.succ = b.succ ↔ a = b :=
begin
  constructor,
  {
    intro h,
    rw [nat.succ_eq_add_one, nat.succ_eq_add_one] at h,
    exact nat.add_right_cancel h,
  },
  intro h,
  rw h,
end

lemma add_left_inj {a b : ℕ} (c : ℕ) : a + c = b + c ↔ a = b :=
begin
  constructor,
  intro h,
  induction c with c hc,
  rw [add_zero, add_zero] at h,
  exact h,
  apply hc,
  rw [nat.add_succ, nat.add_succ] at h,
  rw succ_inj at h,
  exact h,
  intro h,
  rw h,
end

lemma add_right_inj {a b : ℕ} (c : ℕ) : c + a = c + b ↔ a = b :=
begin
  rw [add_comm c, add_comm c],
  exact add_left_inj c,
end

lemma mul_right_inj' {a b : ℕ} (c : ℕ) (hc : c ≠ 0) : c * a = c * b ↔ a = b :=
begin
  have c_pos := nat.pos_of_ne_zero hc,
  constructor,
  intro h,
  exact nat.eq_of_mul_eq_mul_left c_pos h,
  intro h,
  rw h,
end

lemma mul_left_inj' {a b : ℕ} (c : ℕ) (hc : c ≠ 0) : a * c = b * c ↔ a = b :=
begin
  rw [mul_comm _ c, mul_comm _ c],
  exact mul_right_inj' c hc,
end

alias mul_left_inj' ← mul_left_inj
alias mul_right_inj' ← mul_right_inj