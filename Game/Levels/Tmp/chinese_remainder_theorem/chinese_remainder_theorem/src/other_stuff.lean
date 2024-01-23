import data.int.gcd /- ggT / Bézout's lemma-/
import tactic.abel  /- tactis to abel groups-/
import data.nat.modeq /- includes chinese remainder theorem-/
import init.data.nat.basic


-- # Examples 

-- original theorem add_mul_mod_self_left
example (x y z : ℕ) : (x + y * z) % y = x % y :=
begin
  induction z with z h₁, -- Induktionsanfang
  rw [nat.mul_zero], -- Multiplikation mit 0 ausrechnen
  rw [nat.add_zero], -- +0 fällt weg → IA gezeigt
  rw [nat.mul_succ], -- einsetzen von n+1
  rw [ ← nat.add_assoc], -- Klammer wegfallen lassen
  rw [nat.add_mod_right], -- + y fällt weg da y%y = 0
  rw [h₁], -- Hypothese einsetzen
end

-- original therorem nat.add_mul_mod_self_right
example (x y z : ℕ) : (x + y * z) % z = x % z :=
begin
  rw [mul_comm], -- y und z tauschen
  rw [nat.add_mul_mod_self_left], -- Theorem nur anders rum daher mul_comm
end

-- original therorem mul_mod_left 
example (a b : ℕ ) : (a * b) % b = 0 :=
begin
  rw [← nat.zero_add(a * b)], -- eine +0 ergänzen
  rw [nat.add_mul_mod_self_right], -- theorem um es auf 0 zu setzen
  rw [nat.zero_mod], -- 0 % b = 0
end

-- original therorem mul_mod_right
example (a b : ℕ ) : (a * b) % a = 0 :=
begin
  /- Gleicher Weg wie in mul_mod_left nur anders rum
  rw [← nat.zero_add(a * b)], 
  rw [nat.add_mul_mod_self_left],
  rw [nat.zero_mod],
  deswegen kann man es hier auch anders rum machen
  -/

  rw [mul_comm], -- a und b tauschen
  rw [nat.mul_mod_left], -- Theorem von oben verwenden
end

-- original theorem dvd_iff_mod_eq_zero
-- beigetragen zum Verständins von ⟨ , ⟩ 
example (a b : ℤ) : a ∣ b ↔ b % a = 0 :=
begin 
  -- erstes Argument →, zweites Argument ←  
  --exact ⟨int.mod_eq_zero_of_dvd, int.dvd_of_mod_eq_zero⟩,
  constructor, -- Aquivalenz auflösen
  exact int.mod_eq_zero_of_dvd, 
  exact int.dvd_of_mod_eq_zero,
end 

-- theorem modeq_iff_dvd
-- alias nat.modeq.dvd modeq_of_dvd
example (a b n: ℕ): a ≡ b [MOD n] ↔ (n:ℤ) ∣ (b - a) :=
begin
  rw [nat.modeq], --umschreiben von mod zu %
  rw [eq_comm], -- tauschen von a und b
  rw [← int.coe_nat_inj'], -- coehersion wird angewendet
  rw [int.coe_nat_mod, int.coe_nat_mod], -- entfernt Klammern
  rw [int.mod_eq_mod_iff_mod_sub_eq_zero], -- zieht die Gleichung voneinander ab
  rw [int.dvd_iff_mod_eq_zero], -- formt bis zur Gleichheit um
end

--theorem one_dvd (a : α) : 1 ∣ a := dvd.intro a (one_mul a)
-- theorem one_dvd
-- Achtung! | ist \| 
example (a : ℕ ) : 1 ∣ a :=
begin
  use a,
  rw [one_mul],
end