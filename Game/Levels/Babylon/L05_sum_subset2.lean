import Game.Metadata

World "Babylon"
Level 5

Title ""

Introduction
""

open Finset Nat

Statement  (I : Finset ℕ) : ∑ i ∈ I, ((-1 : ℤ)^i + 1) = 2*card { i ∈ I | Even i} := by
  Hint "
    **Du**:  Hier ist jetzt zu zeigen, dass
    $$
    \\sum_\{i \\in I} \\left( (-1)^i + 1 \\right)
    $$
    dasselbe ist wie zweimal die Anzahl der geraden Zahlen in $I$.  Richtig?

    **Robo**:  Richtig.

    **Du**:  Und das ist so, weil … der Ausdruck in der Summe für ungerade $i$ verschwindet,
    und für gerade $i$ gleich $2$ ist. Mmmm …

    **Robo**:  Mach doch wieder mit `trans` ein paar Zwischenschritte.  Zurerst willst du die Summe auf die Menge
    der geraden Indizes einschränken, also auf:
    ```
    ∑ i ∈ \{ i ∈ I | Even i}, ((-1^i + 1)
    ```
    Und danach willst du vermutlich
    ```
    ∑ i ∈ \{ i ∈ I | Even i}, 2
    ```
    als Zwischenschritt verwenden.
  "
  trans ∑ i ∈ { i ∈ I | Even i}, ((-1)^i + 1)
  · symm
    apply sum_subset
    · simp
    · simp
      intro i h hI
      apply hI at h
      rw [Odd.neg_pow]
      ring
      rw [← odd_iff_not_even] at h
      assumption
  · trans ∑ i ∈ { i ∈ I | Even i}, 2
    have : ∀ i ∈ { i ∈ I | Even i}, (-1 : ℤ)^i + 1 = 2 := by
      Hint (hidden := true ) "
        **Robo**:  Dazu hatten wir doch schon mal etwas gesehen, zum Beispiel `Even.neg_pow` und `Odd.neg_pow`.
      "
      intro i hi
      simp at hi
      obtain ⟨hI, heven⟩ := hi
      rw [Even.neg_pow]
      ring
      assumption
    Hint (hidden :=true) "
      **Robo**: Das sieht gut aus. Jetzt bist du so weit, dass du wieter `sum_congr` verwenden kannst.
    "
    apply sum_congr   -- introduced above
    · simp
    · assumption
    Hint (hidden := true) "
      **Robo**: Probier mal wieder `simp`.
    "
    simp
    ring

TheoremTab "∑"

Conclusion "
  **Babylonier**:  Das habt ihr gut gemacht.
"
