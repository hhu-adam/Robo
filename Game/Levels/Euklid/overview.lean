import Mathlib
/-
main things that need to be introduced and explained:

**Drafted for Piazza**:
- Finset
- Finset.erase
- Finset.insert
- Finset.insert_erase

**Drafted for Prado**
- Nat.exists_prime_and_dvd
- Nat.not_dvd_of_between_consec_multiples

**TODO here: Finite/infinite sets:**
- Set.Finite
- Set.Finite.toFinset

**TODO here: Products**
- Finset.prod (∏)
- Finset.prod_pos
- Finset.prod_insert      -- analogous to Finset.add_insert, used in draft of Babylon
-/


open Finset

#check Finset.prod_pos

/-
Finset.prod_pos. {ι : Type} {R : Type} [CommMonoidWithZero R] [PartialOrder R]
  [ZeroLEOneClass R] [PosMulStrictMono R] [Nontrivial R] {f : ι → R} {s : Finset ι}
  (h0 : ∀ i ∈ s, 0 < f i) :
    0 < Finset.prod s fun (i : ι) ↦ f i
-/
