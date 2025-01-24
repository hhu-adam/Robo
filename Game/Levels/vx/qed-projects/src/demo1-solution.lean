
-- import algebra.ring.basic
import ring_theory.ideal.local_ring
import algebra.is_prime_pow
import algebra.char_p.local_ring

import data.nat.factorization.basic -- kauderwelsch



example (R : Type) [ring R] : true := begin
  sorry
end

-- Search for `local_ring`
-- Searh for `charp`

example (R : Type) [ring R] [local_ring R] (q : ℕ) [char_p R q] : q = 0 ∨ ∃ (p n : ℕ), q = p ^ n := begin
  sorry
end

-- is `p` prime?
-- search for `prime_power`

--theorem char_zero_or_prime_power
example (R : Type) [ring R] [local_ring R] (q : ℕ) [char_p R q] :
    q = 0 ∨ is_prime_pow q := begin
  sorry
end

example (R : Type) [ring R] [local_ring R] (q : ℕ) [char_p R q] :
    q = 0 ∨ is_prime_pow q := begin
  -- library_search,
  by_cases q = 0,
  {
    left,
    assumption,
  },
  {
    right,
    unfold is_prime_pow,
    sorry,
  }
end

example (R : Type) [comm_ring R] [local_ring R] (q : ℕ) [char_p R q] :
    q = 0 ∨ is_prime_pow q := begin
  -- library_search, -- didn't work :(
  by_cases q = 0,
  {
    -- this side is simple.
    left,
    assumption,
  },
  {
    right,
    unfold is_prime_pow,

    -- Sei `r = char(R / m)`
    let K := local_ring.residue_field R, -- Oh we need commutativity
    haveI RM_char : char_p K (ring_char K) := by library_search, -- ring_char.char_p K,
    let r := ring_char K,
    let n := (q.factorization) r,

    -- Zeige `q = r ^ n`

    rcases char_p.char_is_prime_or_zero K r with r_prime | r_zero,
    { 
      --case `r ≠ 0`
      sorry, },
    {
      -- case `r = 0`
      have : char_p K 0 := by library_search,
      
      -- haveI : char_zero R := by library_search,

      haveI : char_p K 0 := begin
        library_search, -- ring_char.of_eq r_zero,
      end,

      have : char_zero K,
      {
        exact char_p.char_p_to_char_zero K,
      },

      have : char_zero R := begin
        sorry,
        -- library_search,
      end,
      sorry
    }


  }
end

-- theorem char_p_zero_or_prime_power (R : Type u_1)
-- [comm_ring R] [local_ring R] (q : ℕ) [char_R_q : char_p R q] :
-- q = 0 ∨ is_prime_pow q
