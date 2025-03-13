/-
Additional content needed here for Euklid:

   - L01b: Nat.exists_prime_and_dvd
      {n : ℕ} (hn : n ≠ 1) : ∃ (p : ℕ), Prime p ∧ p ∣ n

     proof would be difficult:  long induction (see below)

   - L03b:  Nat.not_dvd_of_between_consec_multiples
             {m n k : ℕ} (h1 : n * k < m) (h2 : m < n * (k + 1)) : ¬n ∣ m

  Other lemmas mentioned in Maths in Lean:
    - Prime.dvd_mul
      {p m n : ℕ} (pp : Prime p) : p ∣ m * n ↔ p ∣ m ∨ p ∣ n

    - Prime.eq_one_or_self_of_dvd
      {p : ℕ} (pp : Prime p) (m : ℕ) (hm : m ∣ p) : m = 1 ∨ m = p
      (This is just a weaker version of prime_def.)

TODO:  Check whether `specialize` -- currently introduced here in L04 -- is already used earlier
-/


import Mathlib
namespace Nat
alias _root_.Nat.prime_def := prime_def_lt''

/- PART I:  DIVISIBITY (and annoying questions from Guino)-/
/- Prado L01: teaser -/
theorem Robo.prime_two : Prime 2 := by
  decide

/- Prado L02*; Name not needed! -/
-- this is `dvd_add`
example {a b c : ℕ} (h : a ∣ b) (g : a ∣ c) : a ∣ b + c := by
  -- unnecessary but illustrative first step that will be useful later:
  rw [dvd_iff_exists_eq_mul_left] at *
  --
  obtain ⟨x, h⟩ := h
  obtain ⟨y, g⟩ := g
  use x + y
  rw [h, g]
  ring

/- Prado L03* -/
theorem Robo.even_iff_two_dvd {a : ℕ} : Even a ↔ 2 ∣ a := by
  unfold Even
  -- short solution using unnecessary step from L02*
  rw [dvd_iff_exists_eq_mul_left]
  ring
  /- older, long version:
  constructor
  · intro h
    obtain ⟨w, hw⟩ := h
    use w
    rw [hw]
    ring
  · intro h
    obtain ⟨w, hw⟩ := h
    use w
    rw [hw]
    ring
  -/

/- Prado L03a:  annoying question from Guino -/
example : ∃ p : ℕ, Prime p ∧ p ∣ 99 := by
  use 11
  decide

/- Prado L03b: `not_dvd_of_between_consec_multiples` -/
theorem Robo.Nat.not_dvd_of_between_consec_multiples {m n k : ℕ} (h1 : n * k < m) (h2 : m < n * (k + 1)) : ¬n ∣ m := by
  by_contra h_dvd
  obtain ⟨a, ha⟩ := h_dvd
  rw [ha] at h1 h2
  apply Nat.lt_of_mul_lt_mul_left at h1  -- needs to be supplied as a hint
  apply Nat.lt_of_mul_lt_mul_left at h2  -- Note: Nat. is necessary here!
  omega

/- PART II: PRIMES -/
/- Prado L04: `prime_def` -/
example (a p : ℕ) (hp : Prime p) (h : 2 ≤ a) (ha : a ∣ p) : a = p := by
  rw [prime_def] at hp
  obtain ⟨hp₁, hp⟩ := hp
  specialize hp a ha
  obtain hp | hp := hp
  · linarith
  · assumption

/- Prado L04b: `Prime.dvd_mul` -/
example (a b : ℕ) : 5 ∣ (a * b) ↔  5 ∣ a ∨ 5 ∣ b := by
  --constructor
  --intro h
  --repeat rw [even_iff_two_dvd] at *
  rw [Prime.dvd_mul]
  decide


/- Prado L04c: annoying question from Guino -/
-- story:  It seems like Guino is asking an impossible question,
--         but Robo immediately realises that existence is trivial
--
--example : Prime 67280421310721 := by
--  decide  -- maximum recursion depth reached
--
example : ∃ p : ℕ, Prime p ∧ p ∣ 67280421310721 := by
  apply exists_prime_and_dvd
  simp

/- Prado L05:  DELETE -/
/-
  theorem Robo.not_prime_one : ¬ Nat.Prime 1 := by
  decide
-/

/- Prado L06: not really needed; DELETE -/
/-
theorem Robo.prime_dvd_prime_iff_eq {a b : ℕ} (ha : Prime a) (hb : Prime b) :
    a ∣ b ↔ a = b := by
  constructor
  · intro h
    rw [prime_def] at hb
    obtain ⟨_hb_two, hb⟩ := hb
    apply hb at h
    obtain h | h := h
    · have h' := not_prime_one
      rw [← h] at h'
      contradiction
    · assumption
  · intro h
    rw [h]
-/

/- Prado L07*: `∃!`
  `Nat.mul_left_cancel_iff` replaced by more general `mul_eqμl_left_iff`
-/
example {a b : ℕ} (ha : 0 < a) (h : a ∣ b) : ∃! (m : ℕ), a * m = b := by
  obtain ⟨w, hw⟩ := h
  use w
  simp
  constructor
  · rw [hw]
  · intro y hy
    rw [hw] at hy
    rw [mul_eq_mul_left_iff] at hy  -- `mul_eq_mul_left_iff` also used in ROBOTSWANA!
    obtain h | h := hy
    · assumption
    · linarith
    /-
    rw [Nat.mul_left_cancel_iff] at hy -- TODO: _root_.mul_left_cancel_iff takes priority
    · assumption
    · assumption
    -/

/- Prado L08 -/
/-
example : ∃! (p : ℕ), Nat.Prime p ∧ Even p := by
  use 2
  simp
  constructor
  · decide
  · intro y h₁ h₂
    rw [even_iff_two_dvd] at h₂
    rw [prime_dvd_prime_iff_eq] at h₂
    · symm
      assumption
    · decide
    · assumption
-/

/- Prado L08*: BOSS alternative solution without `prime_dvd_prime_iff_eq` -/
example : ∃! (p : ℕ), Nat.Prime p ∧ Even p := by
  use 2
  simp
  constructor
  · decide
  · intro p hp h
    rw [even_iff_two_dvd] at h
    rw [prime_def] at hp
    obtain ⟨h2, hprime ⟩ := hp
    apply (hprime 2) at h
    obtain h | h:= h
    · contradiction
    · symm
      assumption



/- ------------------------------ -/
/-
theorem Robo.Nat.exists_prime_and_dvd (n : ℕ) (hn : n ≠ 1): ∃ (p : ℕ), Prime p ∧ p ∣ n := by
  have (n : ℕ) : ∀ (m : ℕ), 2 ≤ m → m ≤ n → ∃ (p: ℕ), Prime p ∧ p ∣ m := by
    induction' n with d hd
    · intro m hm2 hm0
      use 2
      constructor
      exact prime_two
      have : m = 0 := by linarith
      rw [this]
      use 0
    · intro m hm2 hm
      by_cases hmd : m ≤ d
      · apply hd at hm2
        apply hm2 at hmd
        assumption
      · have : m = d+1 := by
          omega
        by_cases h : ∃ (f : ℕ), f ∣ m ∧ f ≠ 1 ∧ f ≠ m
        · obtain ⟨f, ⟨hf_dvd, hf_1,hf_m⟩⟩ := h
          have : f ≤ d := by
            -- f divides m non-trivially,
            -- so f < m
            -- so f < d + 1
            -- so f ≤ d
            sorry
          apply hd at this
          · obtain ⟨p, hp, hpd⟩ := this
            use p
            constructor
            assumption
            obtain ⟨a, ha⟩ := hpd
            obtain ⟨b, hb⟩ := hf_dvd
            use a*b
            rw [hb,ha]
            ring
          · -- f ≠ 1 and f ≠ 0 (since f divides m and 2 ≤ m)
            -- so 2 ≤ f
            sorry
        · use m
          constructor
          · rw [prime_def]
            constructor
            · assumption
            · push_neg at h
              intro f
              specialize h f
              intro hfm
              apply h at hfm
              rw [imp_iff_not_or] at hfm
              obtain h1 | hm := hfm
              simp at h1
              left
              assumption
              right
              assumption
          rfl
  obtain ⟨⟩ := n
  · use 2
    constructor
    · exact prime_two
    · use 0
  · specialize this (succ n) (succ n)
    apply this
    · omega
    · rfl
-/
