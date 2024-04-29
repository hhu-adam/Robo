import Game.Levels.MatrixTrace.L08_EvalOnEBasis

World "Trace"
Level 9

Title "Matrix"

Introduction
"
Keine fünfzig Meter weiter kommt ihr auf eine kleine Anhöhe. 
Robo zeigt auf einen Punkt in der Ferne.

**Robo**: Schau mal, da liegt es! 

**Du**: Und was *ist* das???

**Robo**:  Weiß nicht.  Aber mein Gefühl sagt mir, diese Zettel sind eine Art Steckbrief.  Schau mal, hier ist noch einer.  Ich glaube, der sagt, wie groß es ist.
"

Conclusion "
  **Du**: Okay. Lass uns vorsichtig näher gehen.
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

  **Robo**: Da gibt es verschiedene Möglichkeiten.  Zum Beispiel:
   `apply nat_mul_inj' (n := n.succ)`!" -- TODO: introduce earlier.
  apply nat_mul_inj' (n := n.succ) -- TODO: is there a better way to write this?
  Hint "(*Stimme von oben*) : Der nächste Schritt ist `rw [←smul_eq_mul, ← LinearMap.map_smul]`,
  aber das kannst du nicht wissen." -- TODO: introduce earlier.
  rw [←smul_eq_mul, ← LinearMap.map_smul]
  Hint "**Du**: Das Argument auf der linken Seite kann ich jetzt als konstante Summe
  darstellen.

  **Robo**: Probier `trans {f} (∑ x : Fin {n}.succ, E {i} {i})`."
  trans f (∑ x : Fin n.succ, E i i)
  · Hint "**Du**: Genau, dann müssen wir für diese erste Gleichheit nur die konstante Summe ausrechnen.

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

-- TODO: Move!
/-- Dieses Theorem sollte eigentlich woanders eingeführt werden -/
TheoremDoc smul_eq_mul as "smul_eq_mul" in "Matrix"
/-- Dieses Theorem sollte eigentlich woanders eingeführt werden -/
TheoremDoc LinearMap.map_smul as "LinearMap.map_smul" in "Matrix"
/-- Dieses Theorem sollte eigentlich woanders eingeführt werden -/
TheoremDoc nat_mul_inj' as "nat_mul_inj'" in "Matrix"

TheoremTab "Matrix"
NewTheorem smul_eq_mul LinearMap.map_smul nat_mul_inj'

#check mul_left_cancel_iff
