import Game.Metadata

World "Euklid"
Level 4
Title ""

/-
Introduction "Nach einer Weile hört ihr Papierrascheln.
Noch dreimal um die Ecke, und ihr findet euch in einem Büro wieder.
„Euklid, Bibliotheksdirektor“ steht an der Tür.

**Euklid**:
Guten Tag!  Das ist ja schön, das sich auch einmal ein paar Besucher hierher verirren.
Wenn ich gewusst hätte, *was* für eine Bibliothek das hier ist,
hätte ich den Posten als Direktor nie angenommen.

**Du**:  Was für eine Bibliothek hätten Sie denn gern?

**Euklid**:  Man hat mir versprochen, hier „unter anderem“ Leansche Varianten
der Schriften meines berühmten Vorfahren zu finden.  Der stammte übringens auch
aus *Ihrem* Universum.  Und nun suche ich schon seit Jahren, im Katalog und in den Büchern selbst,
und finde nur kleinste Bruchstücke.

Schauen Sie, hier habe ich jetzt schließlich selbst angefangen,
eines seiner Ergebnisse zu formulieren.  Vielleicht können Sie mir ja helfen?
"
-/
Introduction "Intro Euklid L04"

open Finset
namespace Nat

Statement : ¬ Set.Finite { p : ℕ | Prime p} := by
  /-
  Hint "**Robo**: Klar, das machen wir.
  Ist doch ein typischer Widerspruchsbeweis:
  Wenn es nur endlich viele Primzahlen gibt, dann ist das Produkt
  aller Primzahlen plus Eins durch keine Primzahl teilbar.
  Andererseits gilt: `exists_prime_and_dvd`.  Widerspruch.
  "
  -/
  Hint "[Hint huqzl] Try proof by contradiction."
  by_contra hf
  -- notation to make equations human-readable:
  Hint "[Hint th0l6] Now construct the new prime.
  Consider the finite set `{hf}.toFinset`,
  define the product of all of these,
  then consider a “new prime” given by that product plus one."
  let all_primes := hf.toFinset
  let prod : ℕ := ∏ p ∈ all_primes, p
  let new_prime : ℕ := prod + 1
  -- As for any natural number > 1, there must be some prime that divides new_prime:
  Hint "[Hint k7r2d] First, establish that, like any natural number greater than one,
        the “new prime” must have a prime factor."
  Hint (hidden := true) "[Hint wai1k] Start with `have … : ∃ p : ℕ, Prime p ∧ p ∣ …`"
  have h_exists_prime_factor : ∃ p : ℕ, Prime p ∧ p ∣ new_prime := by
    Hint (hidden := true) "[Hint nj44y] Establish that the “new prime” is bigger than one,
      and remember `exists_prime_and_dvd`."
    have : 1 < new_prime := by
      have : 0 < prod  := by
        apply Finset.prod_pos
        intro p
        simp [all_primes]
        intro h
        rw [prime_def] at h
        grind
      simp [new_prime]
      assumption
    apply exists_prime_and_dvd
    grind
  -- On the other hand, by construction, no prime divides new_prime:
  Hint "[Hint mnq1z] Great. Now show that, on the other hand, by construction, no prime can divide the “new prime”."
  Hint (hidden := true) "[Hint 7v4d5] Start with `have … : ∀ p : ℕ, Prime p → ¬ p ∣ …`"
  have h_no_prime_divides : ∀ p : ℕ, Prime p →  ¬ p ∣ new_prime := by
    intro p hp
    Hint (hidden := true) "[Hint w0ye0] Introduce the product `q` of all primes apart from `{p}`, and
      establish that the product of all primes is the product of p and q."
    let q := ∏ p' ∈ (all_primes.erase p), (p' : ℕ)
    -- new_prime = p * q + 1 …
    have h : prod = p * q := by
      /- slightly longer version that uses prod_insert: -/
      simp[prod]
      have : p ∈ all_primes := by
        simp [all_primes]
        assumption
      rw[← Finset.insert_erase this]
      apply Finset.prod_insert
      simp
      /- shorter, older version that used mul_prod_erase: -/
      /-
      symm
      apply Finset.mul_prod_erase all_primes id
      simp[all_primes]
      assumption
      -/
    Hint "[Hint 25fac] You now want to apply `not_dvd_of_lt_of_lt_mul_succ`, which we've seen before:
    ```
    not_dvd_of_lt_of_lt_mul_succ \{n k m : ℕ}
       (h1 : n * k < m) (h2 : m < n * (k + 1)) : ¬n ∣ m
    ```
    So bring the goal into a shape to which you can apply that theorem.
    The curly braces around `n`, `k` and `m` mean that these parameters
    are implicit, so you often don't need to mention them.  But you *can* provide them
    with:
    ```
    not_dvd_of_lt_of_lt_mul_succ ( k:= …)
    ```
    "
    simp[new_prime]
    rw [h]
    -- … so it cannot be divisible by p:
    Branch
      have h1 : p * q < p * q + 1 := by
        linarith
      have h2 : p * q + 1 < p * (q + 1) := by
        simp [prime_def] at hp
        linarith
      apply not_dvd_of_lt_of_lt_mul_succ at h1
      apply h1 at h2
      assumption
    apply not_dvd_of_lt_of_lt_mul_succ (n := p) (k:=q) (m := p*q+1)
    · grind
    · simp [prime_def] at hp
      grind
  -- Now we have a contradiction:
  Hint "[Hint 2k3ni] This is looking very promising."
  obtain ⟨p, hp, h_dvd⟩ := h_exists_prime_factor
  specialize h_no_prime_divides p hp
  contradiction

/-
Conclusion "Euklid ist begeistert und tanzt im Kreis.
Er möchte euch fast nicht gehen lassen.
Ihr versprecht, in Kontakt zu bleiben."
-/
Conclusion "Conclusion Euklid L04"
