-- Level name : Mehr zur Null

-- begin hide
import numbers.nat_002b
-- end hide

/-
Noch ein paar Übungen.

Ein Lemma, dass du hierfür brauchst, ist `nat.succ_ne_zero : n.succ ≠ 0`.

- `a + b = 0` genau dann wenn `a = 0` und `b = 0`.
- `a * b = 0` genau dann wenn `a = 0` oder `b = 0`.
-/

/- Hint : At `h: a + b = 0` and `⊢ a = 0`.
Mit `cases b` kannst du wieder eine Fallunterscheidung machen `b = 0` und `b > 0`.
-/

/- Lemma :
Beweise.
-/
lemma add_eq_zero_iff {a b : ℕ} : a + b = 0 ↔ a = 0 ∧ b = 0 :=
begin
  constructor,
  intro h,
  constructor,
  cases b,
  rw add_zero at h,
  exact h,
  rw nat.add_succ at h,
  have q := (a + b).succ_ne_zero,
  contradiction,
  cases a,
  rw zero_add at h,
  exact h,
  rw nat.succ_add at h,
  have h2 := nat.succ_ne_zero (a+b),
  contradiction,
  intro h,
  cases h with h1 h2,
  rw h1,
  rw h2,
end

/- Axiom : nat.succ_ne_zero
`∀ n, n.succ ≠ 0`.
-/

