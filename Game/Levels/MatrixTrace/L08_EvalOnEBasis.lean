import Game.Levels.MatrixTrace.L07_EvalOnEBasis

World "Trace"
Level 8

Title "Matrix"

Introduction
"
A linear functional `f` on the space of `n × n` matrices (for non-zero `n`) which kills
all commutators and moreover satisfies `f(1) = n` has the property that `f (E i i) = 1`
for all `i : Fin n`.
"

open Nat Matrix BigOperators StdBasisMatrix

#check NeZero

/-- Level 8 -/
TheoremDoc Matrix.one_on_diag_ebasis as "one_on_diag_ebasis" in "Matrix"

Statement Matrix.one_on_diag_ebasis {n : ℕ} {f : Mat[n.succ,n.succ][ℝ] →ₗ[ℝ] ℝ}
    (h₁ : ∀ A B, f (A * B) = f (B * A)) (h₂ : f 1 = n.succ) :
    ∀ i, f (E i i) = 1 := by
  intro i
  -- apply Nat.mul_left_cancel
  Hint "**Du**: Ich glaube, ich habe eine Idee! Dafür muss ich aber
  beide Seiten mit `(n + 1)` multiplizieren.

  **Robo**: Da gibt es verschiedene Möglichkeiten.
  Gib folgendes ein: `apply nat_mul_inj' (n := n.succ)`!"
  apply nat_mul_inj' (n := n.succ) -- TODO: is there a better way to write this?
  Hint ""
  rw [←smul_eq_mul, ← LinearMap.map_smul]
  Hint "**Du**: Das Argument auf der linken Seite kann ich jetzt als konstante Summe
  darstellen.

  **Robo**: Probier `trans {f} (∑ x : Fin {n}.succ, E {i} {i})`."
  trans f (∑ x : Fin n.succ, E i i)
  · Hint "**Du**: Genau, dann ist diese erste Gleichheit nur die konstante Summe ausrechnen.

    **Robo**: `simp` kann das sicher komplett vereinfachen."
    unfold E
    simp
  · Hint "**Du**: Als nächstes ziehen wir "
    rw [map_sum]
    trans ∑ i : Fin n.succ, f (E i i)
    · congr
      ext j
      rw [eq_on_diag_ebasis] -- Lvl 5
      assumption
    · rw [← map_sum]
      rw [ebasis_diag_sum_eq_one] -- Lvl 4
      rw [h₂]
      simp
  simp

TheoremTab "Matrix"

#check mul_left_cancel_iff
