-- Level name : Kürzen

-- begin hide
import numbers.nat_007
-- end hide

/-
Ganz ähnlich funktionieren `mul_left_inj'` und `mul_right_inj'`.
`mul_left_inj'` sagt `a * c = b * c ↔ a = b` falls `c ≠ 0`.
-/

/- Lemma : no-side-bar
Beweise.
-/
example (a b : ℕ) (h : 4 * a = 4 * b) : a = b :=
begin
  rw mul_right_inj at h,
  exact h,
  exact nat.succ_ne_zero 3,
end
