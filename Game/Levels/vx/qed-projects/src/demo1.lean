import algebra.ring.basic
import algebra.char_p.basic
import algebra.is_prime_pow
import data.matrix.notation

-- Sei `R` ein lokaler Ring. Dann ist die Charakteristik
-- von `R` entweder `0` oder von der Form `p ^ n`
-- (i.e. a prime power).

theorem demo01 (R : Type) [ring R] (q : ℕ) [char_p R q] :
    q = 0 ∨ is_prime_pow q := begin
  by_cases q = 0,
  {
    left,
    assumption,
  },
  {
    right,
    have h : q ≠ 0,
    {
      library_search,
    },
    sorry
  }
end

instance ee (n : ℕ) [h : fact (0 < n)] : has_zero (fin n) := sorry

example {n : ℕ} [h : fact (0 < n)] (M : matrix (fin n) (fin n) ℤ) :
    true := begin
  let g := M 0 0
end
