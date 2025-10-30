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
Introduction "`INTRO` Intro Euklid L04"

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
  Hint "Try proof by conradiction. For this employ `exists_prime_and_dvd`"
  by_contra hf
  -- notation to make equations human-readable:
  let all_primes := hf.toFinset
  let prod : ℕ := ∏ p ∈ all_primes, p
  let new_prime : ℕ := prod + 1
  -- As for any natural number > 1, there must be some prime that divides new_prime:
  have h_exists_prime_factor : ∃ p : ℕ, Prime p ∧ p ∣ new_prime := by
    have : 1 < new_prime := by
      have : 0 < prod  := by
        apply Finset.prod_pos
        intro p
        simp[all_primes]
        intro h
        rw [prime_def] at h
        linarith
      simp[new_prime]
      assumption
    apply exists_prime_and_dvd
    linarith
  -- On the other hand, by construction, no prime divides new_prime:
  have h_no_prime_divides : ∀ p : ℕ, Prime p →  ¬ p ∣ new_prime := by
    intro p hp
    let q := ∏ p' ∈ (all_primes.erase p), (p' : ℕ)
    -- new_prime = p * q + 1 …
    have h : prod = p * q := by
      /- slightly longer version that uses prod_insert: -/
      simp[prod]
      have : p ∈ all_primes := by
        simp[all_primes]
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
    simp[new_prime]
    rw [h]
    -- … so it cannot be divisible by p:
    apply not_dvd_of_between_consec_multiples (n := p) (k:=q) (m := p*q+1)
    · linarith
    · simp [prime_def] at hp
      linarith
  -- Now we have a contradiction:
  obtain ⟨p, hp, h_dvd⟩ := h_exists_prime_factor
  specialize h_no_prime_divides p hp
  contradiction

/-
Conclusion "Euklid ist begeistert und tanzt im Kreis.
Er möchte euch fast nicht gehen lassen.
Ihr versprecht, in Kontakt zu bleiben."
-/
Conclusion "`CONC` Conclusion Euklid L04"
