/-
Proof 9:   gcd(a, n) | c → a * x ≡ c (mod n)
-/
import data.int.basic
import data.zmod.basic
import data.int.gcd
import ring_theory.bezout


theorem gcd_equiv (a b n : ℤ   ) ( c : ℕ): (int.gcd a n ∣ c)  → ∃ x, a * x ≡ c [ZMOD n]:=
begin
    intro h₁,
    rcases h₁ with ⟨k, hk⟩,  
    let x := a.gcd_a n,
    let y := a.gcd_b n,
    have bez := int.gcd_eq_gcd_ab a n,
    rw hk,
    simp,
    rw bez,
    use x*k,
    rw int.modeq_iff_dvd,
end


theorem gcd_equiv (n a b : ℤ) (c : ℕ): (int.gcd a n ∣ c)  → ∃ x, a * x ≡ c [ZMOD n]:=
begin
    intro h₁,
    rcases h₁ with ⟨k, hk⟩,

    -- I am not sure how you would introduce new variables
    -- For now I just used new assumptions that need to be proved later
    rw hk,

    have bez := int.gcd_eq_gcd_ab a n,
    set z := a.gcd_a n, -- oder `let x := _`
    set y := a.gcd_b n,
    norm_num,
    rw [bez],
    use k*z,
    rw add_mul, 
    rw int.modeq_iff_dvd,
    ring,
    rw mul_comm y,
    rw mul_assoc,
    simp?,
    
    rw ←zmod.eq_iff_modeq_nat,


    simp at *,

    suffices h₃ : ∃ x y, int.gcd a n  = (a * x + n * y), -- (Bezout's identity)
    -- now I need to take the ZMOD on both sides
    -- and then get rid of the unnecessary factors with the Equivalence
    -- but I don't know how

    rw zmod.eq_iff_modeq_nat at hk,
    -- rw int.modeq.refl at h₂,
    -- rw int.modeq_iff_dvd,
    {
        -- suffices h₃: something with bezout?
        -- is_bezout.gcd_eq_sum,
        sorry,
    },
    {
        -- suffices h₂: That's the definition of a | b, but how to transform?
        sorry,
    },
end

#check nat.gcd_eq_gcd_ab