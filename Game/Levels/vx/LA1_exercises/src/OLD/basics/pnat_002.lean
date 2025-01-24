-- Level name : Positive natürliche Zahlen

import basics.numbers.pnat_001

/-
Das Lemma, das du gerade bewiesen hast, findest du als `pnat.ne_zero`
-/

/- Lemma: no-side-bar
Beweise.
-/
example (a b : ℕ+) : (a : ℕ) * b ≠ 0 :=
begin
  by_contradiction h,
  rw nat.mul_eq_zero at h,
  cases h with h h,
  have q := pnat.ne_zero a,
  contradiction,
  have := pnat.ne_zero b,
  contradiction,
end

/- Axiom : pnat.ne_zero
`∀ n : ℕ+, (n : ℕ) ≠ 0`
-/