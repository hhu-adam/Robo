import data.nat.prime
import data.set.finite
import tactic.linarith
import algebra.big_operators.order

-- Damit die Notationen `∏` und `n!` funktionieren.
open_locale big_operators nat

open nat

theorem unenlich_viele_primzahlen :
  ∀ n, ∃ p, nat.prime p ∧ n < p :=
begin
  intro n,

  -- Nimm irgendeinen Primfaktor von `n!` und zeige, dass er nicht in deiner Menge ist.
  let q := min_fac (n! + 1),
  use q,
  have q_prime : nat.prime q,
  { -- Hilfreich: `min_fac_prime`, `factorial_pos`
    sorry,
  },
  {
    sorry,
    -- Führe Widerspruchsbeweis: Nehme an `q ≤ n` und zeige dass dann `q ∣ 1`
    -- (also dass `q` Eins teilt.)
    -- Hilfreich: `not_lt`, `dvd_factorial`, `min_fac_pos`, `min_fac_dvd`, `not_dvd_one`
    -- `dvd_add_iff_right`
  }
end

theorem unenlich_viele_primzahlen₂ :
  ∀ n, ∃ p, nat.prime p ∧ n < p :=
begin
  intro n,

  -- Die Menge aller Primzahlen `≤ n`
  -- Hilfreich um mit dem zu arbeiten sind `set.mem_to_finset` und `set.mem_set_of`
  -- *Bemerkung:* Könnte auch `{x : ℕ | nat.prime x }` nehmen, aber dann wäre der
  -- Endlichkeitsbeweis etwas schwieriger.
  -- So rum ist `ap` per Definition ein `finset`, also eine endliche Menge.
  let all_primes := {x : fin (n + 1) | nat.prime x },
  let ap : finset (fin (n + 1)) := all_primes.to_finset,

  have fp₂ : 0 < ∏ x in ap, (x : ℕ),
  { -- Hilfslemma: Zeige dass das Produkt positiv ist. Benutze `finset.prod_pos` und `prime.pos`
    sorry,
  },

  -- Wähle nun einen Primfaktor vom Produkt aller Primfaktoren `≤ n` plus Eins.
  -- `min_fac` davon ist ein Primfaktor, der dann nicht in der Menge aller Primfaktoren liegt.
  let q := min_fac (∏ x in ap, (x : ℕ) + 1),
  use q,
  have q_prime : nat.prime q,
  { -- Zeige zuerst, dass dieser wirklich eine Primzahl ist. `min_fac_prime` hilft.
    sorry,
  },

  constructor,
  {
    sorry,
  },
  { -- Führe hier einen Widerspruchsbeweis.
    by_contra h,
    rw not_lt at h,

    -- definiere `q` in `fin (n+1)` anstatt in `ℕ`. Per Definition ist `(↑q' : ℕ) = q`.
    -- Das ist nur notwendig, weil wir oben die Menge als Elemente aus `fin (n+1)` definiert haben
    let q' : fin (n + 1) := ⟨q, lt_succ_iff.mpr h⟩,
    have : q' ∈ ap,
    { -- Zeige, dass `q'` als Primzahl `≤ n` in der Menge sein muss.
      sorry,
    },

    have h₁ : (q' : ℕ) ∣ (∏ x in ap, ↑x),
    { -- Zeige, dass ensprechend `q'` das Produkt teilen muss. Hilfreich: `finset.dvd_prod_of_mem`
      sorry,
    },
    -- Jetzt kannst du zeigen, dass in dem Fall `q ∣ 1`, was einen Widerspruch darstellt.
    -- Hilfreich: `min_fac_dvd`, `nat.prime.not_dvd_one`, `nat.dvd_add_iff_right`
    sorry,
  }
end



theorem unenlich_viele_primzahlen_sol :
  ∀ n, ∃ p, nat.prime p ∧ n < p :=
begin
  intro n,

  -- Definiere eine grössere Primzahl
  let q := min_fac (n! + 1),
  use q,
  have q_prime : nat.prime q,
    apply min_fac_prime,
    simp [ne_of_gt, factorial_pos],
  constructor,
  assumption,
  by_contra h,
  rw not_lt at h,
  have h₁ : q ∣ n! := dvd_factorial (min_fac_pos _) h,
  apply q_prime.not_dvd_one,
  exact (nat.dvd_add_iff_right h₁).2 (min_fac_dvd _),
end

theorem unenlich_viele_primzahlen₂_sol :
  ∀ n, ∃ p, nat.prime p ∧ n < p :=
begin
  intro n,

  -- Die Menge aller Primzahlen `≤ n`, und als Hilfe dieselbe as `finset` (`ap`).
  -- Hilfreich um mit den beiden zu arbeiten sind `set.mem_to_finset` und `set.mem_set_of`
  let all_primes := {x : fin (n + 1) | nat.prime x },
  let ap := all_primes.to_finset,

  -- Bemerkung: Könnte auch `{x : ℕ | nat.prime x }` nehmen, aber dann wäre der
  -- Endlichkeitsbeweis etwas schwieriger.

  -- Hilfslemma: Zeige dass das Produkt positiv ist.
  have fp₂ : 0 < ∏ x in ap, (x : ℕ),
  {
    apply finset.prod_pos,
    intros i hi,
    have h : prime i,
    { rwa [set.mem_to_finset, set.mem_set_of] at hi },
    exact prime.pos h,
  },

  let q := min_fac (∏ x in ap, (x : ℕ) + 1),
  use q,
  have q_prime : nat.prime q,
  { apply min_fac_prime,
    simp,
    rw [←ne.def, ←zero_lt_iff],
    assumption,
  },
  constructor,
  assumption,
  by_contra h,
  rw not_lt at h,

  let q' : fin (n + 1) := ⟨q, lt_succ_iff.mpr h⟩,
  have : q' ∈ ap,
  {
    rw [set.mem_to_finset],
    rw set.mem_set_of,
    exact q_prime,
  },

  have h₁ : (q' : ℕ) ∣ (∏ x in ap, ↑x),
  {
    apply finset.dvd_prod_of_mem,
    assumption,
  },
  apply q_prime.not_dvd_one,
  exact (nat.dvd_add_iff_right h₁).2 (min_fac_dvd _),
end



#check nat.exists_infinite_primes


Π (i : ℕ), i