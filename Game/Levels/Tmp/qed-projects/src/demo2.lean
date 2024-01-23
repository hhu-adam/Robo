import number_theory.bernoulli_polynomials
import ring_theory.localization.cardinality
import tactic.fin_cases
import data.zmod.basic
import data.nat.modeq
-- (just random imports)

namespace demo




/-! ## Endlichkeit

`fin n`

is die endliche Menge `{0, 1, …, n-1}`.

-/



/-! Go between `ℕ` and `fin k` -/
def fin_to_N (k : fin 7) : ℕ := ↑k

def N_to_fin (n : ℕ) (hn : n < 10) : fin 10 := ⟨n, hn⟩


-- Change between `k < n + 1` and `k ≤ n`
example (k : ℕ) (h : k ≤ 3) : k < 4 := by library_search
-- nat.lt_succ_iff.mpr h





/-! ## Finite case distinction: -/
example (G : Type) [group G] [fintype G] (h : fintype.card G ≤ 3) : false := begin
  -- defines `k₀` like `let` but also tries to write `k₀`
  -- in the goal wherever possible
  set k₀ := fintype.card G,

  -- Define an element of `fin n` from an element in `ℕ`
  let k : fin 4 := ⟨k₀, nat.lt_succ_iff.mpr h⟩,

  -- One `fin n` one can use `fin_cases k` to make a case distinction
  fin_cases k,

  -- Now we look at the cases `k = 0`, `k = 1`, …
  { sorry },
  { sorry },
  { sorry },
  { sorry },
end





/-! ## Indexed types -/

-- Sei (Vᵢ)ᵢ eine Familie von Unterwektorräumen von `V`

variables {K V : Type} [field K] [add_comm_monoid V] [module K V]

variables (ι : Type) (T : ι → submodule K V) (i : ι)

#check T i

#check ℕ
#check ℕ → ℤ 

variables {ι₂ : Type} [fintype ι₂] (T₂ : ι → submodule K V)

-- V₀ … Vₙ₋₁
variables (n : ℕ) (T₃ : fin n → submodule K V)


variables (m : ℕ) (G : fin m → Type*) [∀ i, group (G i)]

variables (m₂ : ℕ) (G₂ : fin m₂ → Type*) [Π i, group (G i)]



#eval (3 : fin 5) + (6 : fin 5)



/-! ## Modulo

`a ≡ b [MOD n]`, `n.modeq a b`, `fin n`, `zmod n`. 
-/

example (a b n : ℕ) (h : n.modeq a b) : false := begin
  sorry
end

example (a b n : ℕ) (h : a ≡ b [MOD n]) : false := begin
  sorry
end

example (n : ℕ) (a b : fin n) (h : a = b) : (a : ℕ) ≡ ↑b [MOD n] := begin
  rw ←zmod.eq_iff_modeq_nat,
  rw h,
end

#check nat.add_modeq_left
#check zmod.eq_iff_modeq_nat

end demo