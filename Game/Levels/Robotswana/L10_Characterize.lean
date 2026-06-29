import Game.Levels.Robotswana.L09_EvalOnEBasis

World "Robotswana"
Level 10

Title "" -- "Trace"

/-
Introduction
"
Ihr schleicht euch langsam an.

**Du** (**flüsternd**): Ich glaube, du hattest Recht.  Diese Zettel sind eine Art Steckbrief!
Und sie beschreiben dieses Wesen hier eindeutig!

**Robo**: Wie meinst du das?

**Du**: Schau doch, seine Größe, seine Vorliebe für Kommutatoren, und all die anderen Sachen,
damit kann es eindeutig identifiziert werden!

**Robo**: Das musst du mir genauer erklären.

**Du**:  Ich versuch's mal. Gibt es in Leansch einen Namen für die Spur?

**Robo**: Ja klar, die heißt natürlich `trace`.  Manche Formalosophen nennen sie auch liebevoll Tracy.

Du nimmst einen der Pergamentfetzen und schreibst auf die Rückseite.
"
-/
Introduction "Intro Robotswana L10: Introduce `trace`"

/-
Conclusion "
**Robo**: Tatsache. Du hattest Recht.

Ihr beobachtet voller Entzücken dieses offenbar einzigartige Wesen auf diesem Planeten.

Als ihr näher kommt, scheint euch Tracy zu bemerken.  Aber es scheint dadurch keinesfalls gestört
zu sein.
"
-/
Conclusion "Conclusion Robotswana L10"

open Nat Matrix Finset

/---/
TheoremDoc Matrix.trace_eq as "trace_eq" in "Matrix"

Statement Matrix.trace_eq {n : ℕ} (f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ)
    (h₁ : ∀ A B, f (A * B) = f (B * A)) (h₂ : f 1 = n) :
    trace = f := by
  Hint "Explain that each `f` has stated properties"
  Hint (hidden := true) "Use `ext`!"
  ext A
  Hint "Rewrite `A` in `f {A}` as sum of basis elements.  Use `nth_rw`, `nth_rw 2` with `matrix_eq_sum_ebasis`"
  nth_rw 2 [matrix_eq_sum_ebasis A]
  simp [map_sum]
  change A.trace = ∑ i : Fin n, ∑ j : Fin n, A i j * f (E i j)
  Hint (hidden := true) "[Hint kqwz] prove `A i j * f (E i j) = if i = j then A i i else 0`"
  have (i j : Fin n) : A i j * f (E i j) = if i = j then A i i else 0
  · by_cases h_ij : i = j
    rw [if_pos h_ij, h_ij]
    rw [one_on_diag_ebasis h₁ h₂] -- L09
    ring
    rw [if_neg h_ij]
    rw [zero_on_offDiag_ebasis h_ij h₁] -- L07
    ring
  simp [this]
  rfl

NewDefinition Matrix.trace
TheoremTab "Matrix"
