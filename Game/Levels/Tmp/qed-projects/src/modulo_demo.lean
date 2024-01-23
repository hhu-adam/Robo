import data.zmod.basic
import tactic.fin_cases

#eval 3453 % 27
example : 3453 % 27 = 24 := by refl

/-- `a = b` in `ℤ/(n)` genau-dann-wenn `a ≡ b (mod n)` -/
example (n : ℕ) {a b : ℕ} : (a : zmod n) = ↑b ↔ a ≡ b [MOD n] :=
begin
  exact zmod.eq_iff_modeq_nat n,
end

#check zmod.eq_iff_modeq_nat

instance can_lift' (n : ℕ) : can_lift ℕ (zmod n) (zmod.val) (λ k, k < n) := { prf := begin
  intros x hx,
  use x,
  apply zmod.val_cast_of_lt,
  assumption,
end }

example (a : ℕ) (h : ¬ (a % 3 = 0)) : a % 3 = 1 ∨ a % 3 = 2 := begin

  -- Nicht gebraucht, aber als Demonstration
  change ¬ (a % 3 = 0 % 3) at h,

  -- Schreibe `h` und das Goal äquivalent um.
  change ¬ (a ≡ 0 [MOD 3]) at h,
  change  (a ≡ 1 [MOD 3]) ∨ (a ≡ 2 [MOD 3]),

  -- Wechsle zu `ℤ/(3)`
  simp_rw [←zmod.eq_iff_modeq_nat 3] at *,

  -- Jetzt will ich `↑a` als `a₁` benennen. Offenbar braucht man dafür `generalize'`.
  generalize' ha₁ : (a : zmod 3) = a₁,
  rw ha₁ at *,

  fin_cases a₁,
  contradiction,
  left,
  tauto,
  right,
  tauto,
end

-- TODO!!!!

lemma number_squares_half () :


-- synth: fintype from set.finite