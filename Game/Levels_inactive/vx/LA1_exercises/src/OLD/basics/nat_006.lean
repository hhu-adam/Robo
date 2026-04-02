-- Level name : Mehr zur Null

-- begin hide
import basics.numbers.nat_005
-- end hide

/- Lemma :
Zeige: `a * b = 0` genau dann wenn `a = 0` oder `b = 0`.
-/
lemma mul_eq_zero {a b : ℕ} : a * b = 0 ↔ a = 0 ∨ b = 0 :=
begin
  constructor,
  intro h,
  induction a with a ha,
  left,
  refl,
  right,
  rw nat.succ_mul at h,
  rw add_eq_zero_iff at h,
  exact h.2,
  intro h,
  cases h with h h,
  rw h,
  rw zero_mul,
  rw h,
  rw mul_zero,
end


