import number_theory.arithmetic_function
-- random import, der sicher die Grundlagen importiert

#check nat.choose_eq_factorial_div_factorial

-- Damit man das `nat.` bei Theoremen weglassen kann
open nat 

-- Damit `p!` als Notation funktioniert
open_locale nat

lemma dvd_or_dvd {p a b : ℕ} (h : nat.prime p) (g : p ∣ a * b) : p ∣ a ∨ p ∣ b := begin
  exact (prime.dvd_mul h).mp g
end

/--
Wenn `p` nicht `n` teilt (`n` ist ein Faktor von `p!`),
dann teilt `p` die differenz `p! / n`.
-/
example (p n : ℕ) (h₀ : nat.prime p) (h₁ : n ∣ p!) (h₂ : ¬ (p ∣ n)) : p ∣ (p! / n) := begin
  -- 1) Zeige dass `p! / n * n = p!`. Das ist nicht trivial weil z.B. `(3 / 2) * 2 = 1 * 2 = 2 ≠ 3`
  have h₃ : p! = (p! / n) * n,
  {  rw nat.div_mul_cancel h₁, },
  -- Das sollte auch schneller gehen: `p` teilt `p!`.
  have h₄ : p ∣ p!,
  {
    apply dvd_factorial,
    exact prime.pos h₀,
    tauto,
  },

  -- Schreibe `h₄` um zu: `p ∣ (p! / n) * n`
  rw h₃ at h₄,

  -- `dvd_or_dvd` ist sagt `p | a * b` impliziert `p` teilt einen der Faktoren.
  -- Mache dann eine Fallunterscheidung welchen von beiden es teilt.
  have h₅ := dvd_or_dvd h₀ h₄,
  rcases h₅ with h₅ | h₅,
  -- Fall 1: genau was wir zeigen wollten
  assumption,
  -- Fall 2: Widerspruch, da `p` diesen Faktor nicht teilen kann (`h₂`).
  contradiction,
end