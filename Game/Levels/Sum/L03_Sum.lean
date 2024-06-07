import Game.Metadata

open Finset

World "Sum"
Level 3

Title "endliche Summe"

Introduction
"
Ihr schaut euch den nächsten Turm an."

open BigOperators

/-- $\sum_{i=0}^{n-1} (i + 1) = n + \sum_{i=0}^{n-1} i$. -/
Statement (n : ℕ) : ∑ i : Fin n, (i + 1) = n + (∑ i : Fin n, i) := by
  Hint "**Du**: Hmm, wieder `simp`?

  **Robo**: Nicht ganz. `simp` benutzt nur Lemmata, die klar eine Vereinfachung darstellen.
  Im Lean-Duden sind diese Lemmata mit `@[simp]` markiert.
  Hier brauchen wir aber folgende Identität:

  $$
  \\sum_\{i = 0}^n a_i + b_i = \\sum_\{i = 0}^n a_i + \\sum_\{j = 0}^n b_j
  $$

  **Robo**: Und da bei dieser Identität unklar ist, welche Seite „einfacher“ ist, wird so ein Lemma nicht mit
  `@[simp]` markiert.

  **Du**: Hat diese Gleichheit denn wenigstens einen Namen.

  **Robo**: Sie heißt `sum_add_distrib`.
  "
  rw [sum_add_distrib]
  Hint "**Robo**: Die zweite Summe `∑ x : Fin n, 1` kann jetzt aber mit
  `simp` zu `n` vereinfacht werden."
  simp
  Hint "**Robo**: Bis auf Umordnung sind jetzt beide Seiten gleich!

  **Du**: Dann greift jetzt wohl `ring`!

  **Robo**: Genau! Und alternativ könntest du mit `rw [add_comm]` die Arbeit von `ring`
  auch manuell machen."
  ring

/---/
TheoremDoc Finset.sum_add_distrib as "sum_add_distrib" in "Sum"

NewTheorem Finset.sum_add_distrib
-- TODO: where does add_comm belong?
TheoremTab "Sum"

Conclusion "Der Babylonier macht ein sehr zufriedenes Gesicht."
