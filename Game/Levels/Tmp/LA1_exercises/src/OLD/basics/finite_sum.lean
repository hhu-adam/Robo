import algebra.big_operators.fin
import tactic.ring
import tactic.linarith
import algebra.algebra.basic
import algebra.big_operators.default

open_locale big_operators

theorem nat_succ (n : ℕ) : nat.succ n = n + 1 := rfl

lemma hh1 (n m : ℕ) (h : 2 * m = n) : m = n / 2 :=
begin
  rw [←h],
  symmetry,
  apply nat.mul_div_right,
  simp?,
end

example (n : ℕ) : 2 * (∑ i : fin (n + 1), ↑i) = n * (n + 1) :=
begin
  induction n with n hn,
  simp,
  rw [fin.sum_univ_cast_succ],
  simp [nat_succ],
  rw [mul_add, hn],
  ring,
end

example (n : ℕ) : (∑ i : fin (n ), (↑i + 1)) = (∑ i : fin (n ), ↑i) + (∑ i : fin (n ), 1) :=
begin
  exact finset.sum_add_distrib,
end

example (n : ℕ) (i : fin n) : (i.cast_succ : ℕ) = i := fin.coe_cast_succ i

