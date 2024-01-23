import data.int.gcd /- ggT / Bézout's lemma-/
import tactic.abel  /- tactis to abel groups-/
import data.nat.modeq /- includes chinese remainder theorem-/
import init.data.nat.basic
--import data.zmod.basic /- Lean stürzt bei mir ab wenn ich das importiere-/

#check nat.chinese_remainder'
#check nat.chinese_remainder

/-  
# Useful definitions
`a ≡ b [MOD n]` is notation for `nat.modeq n a b` 
gcd = greatest common divisor
ggT(m,n) = d * m  + c * n = 1 - wird gefunden durch nat.xgcd - `gcd n m = n * c + m * d`
`k = a * (m * d) + b * (c * n)`
nat.lcm n m - `n * m / (gcd n m)`
convert modeq_one --> umschreiben of the theorem
coprime means ggT = 1
-/

-- # Beispiel zum Chinesischen Restsatz
-- ∃ k : ℕ, k ≡ a [MOD 3] ∧ k ≡ b [MOD 5]
example (a b: ℕ) :  {k // k ≡ 2 [MOD 3] ∧ k ≡ 3 [MOD 5]}:=
begin
  have co_prime: nat.coprime 3 5,
    {
      -- hier muss nur gezeigt werden das ggT(3,5) = 0
      sorry,
    },
  -- vorher hatte ich die Variablen a und b noch
  -- aus vereinfachungs gründen jedoch direkt gesetzt
  --let a := 2,
  --let b := 3,
  -- wende den chinesischen Restsatz aus der Library an 
  have h := nat.chinese_remainder co_prime 2 3,
  tauto,
end


-- # Chinesischen Restsatz
example (m n : ℕ) (co : n.coprime m) (a b : ℕ) (h : a ≡ b [MOD nat.gcd n m]):
{k // k ≡ a [MOD n] ∧ k ≡ b [MOD m]} :=
  if hn₁: n = 0 then -- Wenn n = 0 dann:
    ⟨ a, -- setze k = a
      begin -- Beweise nun die Aussage
      rw [hn₁] at h, -- setze n = 0 in h
      have hn₂ : nat.gcd 0 m = m, -- ggT(0,m)=m
      rw[nat.gcd_zero_left], -- umschreiben mit ggT(0,m) = m
      rw [hn₂] at h, -- umschreiben von h
      split, -- split ∧ in 2 Aussagen
      refl, -- umschreiben mit Reflexivität
      exact h, -- Aussage ist h
      end -- Ende vom Beweis
    ⟩
  else -- Hypothese hn₁: ¬n = 0 
  if hm₁: m = 0 then -- Wenn m = 0 dann:
    ⟨ b, -- setze k = b
      begin -- Beweise nun die Aussage
      rw [hm₁] at h, -- setze m = 0 in h
      have hm₂ : nat.gcd n 0 = n, -- ggT(n,0)=n
      rw [nat.gcd_zero_right], -- umschreiben mit ggT(n,0)=n
      rw [hm₂] at h, -- umschreiben von h
      split, -- split ∧ in 2 Aussagen
      exact h.symm, -- a ≡ b äuqivalent zu b ≡ a
      refl, --umschreiben mit Reflexivität
      end -- Ende vom Beweis
    ⟩
  else -- Hypothesen hm₁: ¬m = 0  und hn₁: ¬n = 0 
    -- `gcd n m = n * c + m * d`
    ⟨let (c, d) := nat.xgcd n m in int.to_nat (((a * (m * d) + b * (c * n)) / nat.gcd n m) % nat.lcm n m),
      begin
        rw [nat.xgcd_val], -- setze `c = n.gcd_a m` und `d = n.gcd_b m` in n.xgcd m ein
        dsimp [_example._match_1], -- setze die Variablen ein
        rw [nat.modeq_iff_dvd, nat.modeq_iff_dvd], -- umformen von mod zu % schreibweise
        split,
        -- erste Seite
        sorry,
        -- zweite Seite
        sorry,
      end
    ⟩
