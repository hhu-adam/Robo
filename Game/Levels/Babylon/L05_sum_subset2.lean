import Game.Metadata

World "Babylon"
Level 5

Title "[Babylon.L05] Title"

Introduction "[Babylon.L05] Introduction"

open Finset Nat

Statement  (I : Finset ℕ) : ∑ i ∈ I, ((-1 : ℤ)^i + 1) = 2*card { i ∈ I | Even i} := by
  /-
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
    ∑ i ∈ \{ i ∈ I | Even i}, ((-1)^i + 1)
    ```
    Und danach willst du vermutlich
    ```
    ∑ i ∈ \{ i ∈ I | Even i}, 2
    ```
    als Zwischenschritt verwenden.
  "
  -/
  Hint "Goal is to show that $$ \\sum_\{i \\in I} \\left( (-1)^i + 1 \\right) $$ is equal to twice the amount of
  even numbers in $I$. Note that sum disappears for uneven $i$. For even $i$ the sum is $2$. Use `trans` to
  constrain sum to ``` ∑ i ∈ \{ i ∈ I | Even i}, ((-1)^i + 1) ``` and then use ``` ∑ i ∈ \{ i ∈ I | Even i}, 2 ```
  as intermediate step."
  trans ∑ i ∈ { i ∈ I | Even i}, ((-1)^i + 1)
  · Branch
      rw [sum_subset]
      /-
      Hint "
        **Robo**:  Das sieht irgendwie falsch aus …
        Vielleicht solltest du `sum_subset` lieber rückwarts anwenden.
        Oder vor diesem Schritt mit `symm` die Gleichung umdrehen.
        "
      -/
      Hint "Try `sum_subset` from the other side or `symm` beforehand"
    symm
    apply sum_subset
    · simp
    · simp
      intro i h hI
      apply hI at h
      rw [Odd.neg_pow]
      ring
      assumption
  · trans ∑ i ∈ { i ∈ I | Even i}, 2
    have : ∀ i ∈ { i ∈ I | Even i}, (-1 : ℤ)^i + 1 = 2 := by
      /-
      Hint (hidden := true ) "
        **Robo**:  Dazu hatten wir doch schon mal etwas gesehen, zum Beispiel `Even.neg_pow` und `Odd.neg_pow`.
      "
      -/
      Hint "Familiar situation: try `Even.neg_pow` or `Odd.neg_pow`"
      intro i hi
      simp at hi
      obtain ⟨hI, heven⟩ := hi
      rw [Even.neg_pow]
      ring
      assumption
    /-
    Hint (hidden :=true) "
      **Robo**: Das sieht gut aus. Jetzt bist du so weit, dass du wieter `sum_congr` verwenden kannst.
    "
    -/
    Hint "Now oyu can use `sum_congr`"
    apply sum_congr   -- introduced above
    · simp
    · assumption
    /-
    Hint (hidden := true) "
      **Robo**: Probier mal wieder `simp`.
    "
    -/
    Hint (hidden := true) "Try out `simp` again"
    simp
    ring

TheoremTab "∑ Π"

/-
Conclusion "
  **Babylonier**:  Das habt ihr gut gemacht.
"
-/
Conclusion "Conclusion Babylon L05"
