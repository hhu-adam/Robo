import data.nat.prime
import data.nat.modeq
import algebra.group_power.ring
import data.nat.choose.sum
import data.zmod.basic
import data.nat.factorial.basic
import algebra.big_operators.fin
import data.nat.choose.dvd

open_locale big_operators

--Hilfslemma: (x+y)^p ≡ x^p + y^p [MOD p]
theorem freshmansDream (x y p k : ℕ) (prime_p : nat.prime p): (x + y) ^ p ≡ x ^ p + y ^ p [MOD p] :=
begin
-- Binomialsatz anwenden
  have h₁ : (x + y) ^ p = (finset.range (p + 1)).sum (λ (m : ℕ), x ^ m * y ^ (p - m) * ↑(p.choose m)),
  {
    apply add_pow,  
  },
  rw[h₁],
  --Alle Summanden bis auf den ersten und letzten sind 0 MOD p,
  --da p.choose k ≡ 0 MOD p für 0 < k < p
  have h₂ : (0 < k ∧ k < p) → p.choose k ≡ 0 [MOD p],
  {
    intro h₂,
    rcases h₂ with ⟨a, b⟩,
    rw[nat.modeq_zero_iff_dvd],
    apply nat.prime.dvd_choose_self,
    {
      assumption,
    },
    {
      assumption,
    },
    assumption,
    
  },
  --Ersten und letzten Summanden abspalten
  rw[←fin.sum_univ_eq_sum_range], --finset.range in fin umschreiben, damit wir die richtigen Lemmas haben
  rw[fin.sum_univ_succ],          --Ersten Summanden abspalten
  simp,
  ring_nf,
  --Summe so umschreiben, dass der letzte Summand abgespalten werden kann
  --Dafür muss p ≠ 0
  have h₃ : p ≠ 0,                
  {
  exact nat.prime.ne_zero prime_p,--p ist Primzahl, also ≠ 0
  },
have := nat.exists_eq_succ_of_ne_zero h₃, --p ≠ 0, also existiert eine Zahl davor
  rcases this with ⟨p', hp'⟩,
  subst hp',
  rw[fin.sum_univ_cast_succ],   --Letzten Summanden abspalten
  simp,
  ring_nf,
  rw[nat.succ_eq_add_one],
  apply nat.modeq.add_left,     --beide Seiten mit y-Term substrahieren
  have h₄ : ∑ (x_1 : fin p'), x ^ (↑x_1 + 1) * y ^ (p' - ↑x_1) * (p' + 1).choose (↑x_1 + 1) + x ^ (p' + 1) ≡ x ^ (p' + 1) [MOD p' + 1] ↔ 
  ∑ (x_1 : fin p'), x ^ (↑x_1 + 1) * y ^ (p' - ↑x_1) * (p' + 1).choose (↑x_1 + 1) + x ^ (p' + 1) ≡ 0 + x ^ (p' + 1) [MOD p' + 1],
  {
    simp,
  },
  rw[h₄],
  apply nat.modeq.add_right,    --beide Seiten mit x-Term substrahieren
  rw[nat.succ_eq_add_one] at h₂ h₁ prime_p h₃,
  --mit h₂ die restliche Summe ≡ 0 [MOD p'+ 1] setzen
  sorry,
   
end

--FermatsLittleTheorem: a^p ≡ a [MOD p]
example (a p : ℕ) (prime_p : nat.prime p): ((a ^ p)) ≡  a [MOD p]:=
begin
  induction a with d hd,
  --Induktionsanfang
  {
    rw [zero_pow'],
    exact nat.prime.ne_zero prime_p,
  },
  --Induktionsschritt
  {
     rw[nat.succ_eq_add_one],
    have h₂ : (d + 1) ^ p ≡  d ^ p + 1 ^ p [MOD p],
    --Zeige (d+1)^p ≡ d^p + 1^p [MOD p] mit Hilfslemma
    {
      apply freshmansDream,   --Hilfslemma anwenden
      assumption,
      assumption,
    },
    have h₃ : d ^ p + 1 ^ p ≡ d + 1 [MOD p],
    {
      rw[one_pow],            --1 ^ p = 1 (beeindruckend)
      apply nat.modeq.add_right,
      assumption,             --Induktionsvoraussetzung benutzen
    },
    --Transitivität von MOD ausnutzen
    transitivity,
    {
      assumption,
    },
    {
      assumption,
    }  
  }
end
