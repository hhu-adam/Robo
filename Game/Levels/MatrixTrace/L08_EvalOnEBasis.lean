import Game.Levels.MatrixTrace.L07_EvalOnEBasis

World "Trace"
Level 8

Title "Matrix"

Introduction
"
Keine fünfzig Meter weiter kommt ihr auf eine kleine Anhöhung. In der Ferne fählt dir sofort
ein dunkler Punkt auf, auf den Robo auch zeigt.

**Du**: Schau mal, das wird es wohl sein! Und von hier kann man auch perfekt seine Grösse
abschätzen.

**Robo**: Sieht so aus, als währen ihm alle diagonalen Elemente `E i i` nicht nur \"gleich\"
sondern \"eins\". Aber können wir mehr herausfinden?
"

Conclusion "
  **Du**: Los, lass uns näher gehen.
"

open Nat Matrix BigOperators StdBasisMatrix

/---/
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
  · Hint (hidden := true )"**Du**: Als nächstes ziehen wir die Funktion in die Summe rein."
    Hint "**Du**: Und jetzt möchte ich die Gleichung durch einen Zwischenschritt
    `∑ i, f (E i i)` zeigen."
    trans f (∑ i, E i i)
    · Branch
        congr
        Hint "**Du**: Nein, das ist jetzt mathematisch falsch!"
      Hint (hidden := true) "**Robo**: Jetzt wieder `congr`-`ext`?

      **Du**: Nein, zuerst, die Funktion in die Summe rein, sonst klappt das nicht."
      rw [map_sum]
      Hint "**Du**: Nochmals!"
      rw [map_sum]
      congr
      ext j
      Hint "**Du**: Und das war ein Resultat, welches wir auf dem Weg gefunden haben."
      Hint (hidden := true) "**Robo**: `eq_on_diag_ebasis` sagt meine Speicherplatte."
      rw [eq_on_diag_ebasis] -- Lvl 5
      assumption
    · Hint (hidden := true) "**Robo**: Das sieht nach `ebasis_diag_sum_eq_one` aus."
      rw [ebasis_diag_sum_eq_one] -- Lvl 4
      rw [h₂]
      simp
  simp

TheoremTab "Matrix"

#check mul_left_cancel_iff
