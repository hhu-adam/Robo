import Game.Metadata

World "Euklid"
Level 3
Title ""

/-
Introduction "
  Ihr müsst ein ganzes Stück laufen, um das nächste aufgeschlagene Buch zu finden.
  Robo hat angefangen, einen roten Faden auszurollen, damit ihr den Weg zurückfindent.
"
-/
Introduction "`INTRO` Intro Euklid L03"

open Finset
namespace Nat

Statement (hf : Set.Finite { p : ℕ | Prime p}) : ∃ (a : ℕ), a > 0 ∧ ∀ (p : ℕ), Prime p → p ∣ a := by
  -- tauto -- If we don't insist a > 0, tauto solves this!
  /-
  Hint "**Robo**: Oho!  Das sieht ja ganz interessant aus:
  Wenn wir annehmen, dass es nur endlich viele Primzahlen gibt,
  dann gibt es auch eine positive natürliche Zahl, die von jeder Primzahl geteilt wird.

  **Du**:  Ja, klingt ein wenig absurd, aber richtig.  Und der Beweis?  Als erste Zeile steht hier
  `let all_primes := hf.toFinset`.  Ist das in irgendeiner Form sinnvoll?

  **Robo**:  Sehr sinnvoll sogar!
  Um die Aussage zu zeigen, will man ja sicherlich das Produkt über alle Primzahlen betrachten.
  Und damit das überhaupt syntaktisch möglich ist, musst du diese Menge aller Primzahlen
  als `Finset` betrachten.  Die erste Zeile macht genau das:  sie benutzt die Annahme `hf`,
  um aus `\{ p : ℕ | Prime p} : Set ℕ` eine endliche Teilmenge `\{ p : ℕ | Prime p} : Finset ℕ`
  zu machen.

  **Du**:  Okay, ich probier das mal.
  "
  -/
  Hint "Try `let all_primes := hf.toFinset`"
  let all_primes := hf.toFinset
  /-
  Hint "
    **Du**:  Und die nächste Zeile?

    `all_primes.bubblewrap = blister cong foo`

    Ist die auch noch sinnvoll?

    **Robo**:  Nein, die ist wieder hochgradiger Schwachsinn.
    Wie gesagt, du willst jetzt sicherlich das Produkt aller dieser Zahlen benutzen.
    Das Produktzeichen schreibst du als `\\prod`."
  -/
  Hint "Try `\\prod`"
  use ∏ p ∈ all_primes, p
  /-
  Hint "
    **Robo**:  Bravo.

    **Du**:  Hatten wir nicht eben schon ein paar Sachen gezeigt, die jetzt ziemlich nützlich wäre.

    **Robo**: Ups.  Ja, hatten wir, aber habe ich leider nicht abgespeichert.
    Musst du leider noch einmal rekonstruieren, wie die Argumente gingen.
    "
  -/
  Hint "Try `constructor`"
  constructor
  · -- Hint "**Robo**:  Hier sollte `Finset.prod_pos` wieder weiterhelfen."
    Hint "Try `Finset.prod_pos`"
    apply Finset.prod_pos
    intro p
    simp [all_primes]
    intro h
    rw [prime_def] at h
    linarith
  · intro p hp
    -- previous lemma would be useful now, but want to practise!
    have hp' : p ∈ all_primes := by
      /-
      Hint (hidden := true) "
        **Robo**: Wenn `simp` hier nicht funktioniert, musst du `simp` vielleicht
        die Definition von `all_primes` mit auf den Weg geben.  Also `simp [all_primes]`.
        "
      -/
      Hint (hidden := true) "Try `simp [all_primes]`"
      simp [all_primes]
      assumption
    rw [← insert_erase hp']
    rw [prod_insert]
    · use ∏ x ∈ all_primes.erase p, x
    · simp


/-- Ist eine Teilmenge `A : Set T` mit der Annahme `h : Set.Finite A` gegeben,
so ist `h.toFinset : Finset T` dieselbe Teilmenge `A`,
aber nun explizit als endliche Teilmenge aufgefasst. -/
TheoremDoc Set.Finite.toFinset as "toFinset" in "Set"

NewTheorem Set.Finite.toFinset
NewDefinition Set.Finite

/-
Conclusion "
  Ihr schlagt einen Gang ein, indem gleich mehere Bücher auf dem Boden liegen.
  Aber keines ist aufgeschlagen.
  An der nächsten Kreuzung zweigt wieder einen Gang ab mit mehreren Büchern auf dem Boden.

  **Du**:  Ist das vielleicht eine Spur?

  **Robo**: Folgen wir ihr!
 "
-/
Conclusion "`CONC` Conclusion Euklid L03"
