-- Level name : Kürzen

-- begin hide
import numbers.nat_006b
-- end hide

/-
Die letzte Gruppe von wichtigen Lemmas sind `add_left_inj`, `add_right_inj`,
`mul_left_inj'` und `mul_right_inj'`.
`add_left_inj` sagt `∀ c, a + c = b + c ↔ a = b`.
-/

/- Hint : rw at
Du kannst mit `rw` nicht nur das Goal umschreiben, mit `rw one_mul at h` kannst du
stattdessen die Annahme `h` umschreiben.
-/

/- Lemma : no-side-bar
Beweise.
-/
example (a b : ℕ) (h : a + 1 = b + 1) : a = b :=
begin
  rw add_left_inj at h,
  exact h,
end

/- Lemma : no-side-bar
Beweise.
-/
example (a b : ℕ) (h : 4 * a = 4 * b) : a = b :=
begin
  rw mul_right_inj at h,
  exact h,
  exact nat.succ_ne_zero 3,
end

/- Axiom : add_left_inj c
`a + c = b + c ↔ a = b`.
-/

/- Axiom : add_right_inj c
`c + a = c + b ↔ a = b`.
-/

/- Axiom : mul_left_inj' c
`(c ≠ 0) → (a * c = b * c ↔ a = b)`.
-/

/- Axiom : mul_right_inj' c
`(c ≠ 0) → (c * a = c * b ↔ a = b)`.
-/
