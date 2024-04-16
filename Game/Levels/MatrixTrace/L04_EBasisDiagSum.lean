import Game.Levels.MatrixTrace.L03_MatrixEqSum

World "Trace"
Level 4

Title "Einheitsmatrix"

Introduction
"
**Du**: Zeig mal, was hast du da? Was zur Einheit der Matrizen? Passend für die
vermeintliche Versammlung von vorhin.

**Robo**: Und schau, scheint so als hättest du vorhin das richtige angeschaut. Hier
kann man soweit ich sehe gleich mit `matrix_eq_sum_ebasis` beginnen.
Kannst du mal schauen, ob das stimmt?

**Du**: Ich frage mich, ob wir noch wichtiges auf dem Platz zurückgelassen haben?

**Robo**: Egal, jetzt sind wir schon ein gutes Stücken weiter, aber komm, hilf mir mal.
"

Conclusion "**Du**: Ich habe langsam eine Vermutung, dass wir jemandem folgen, der
sich doch für die Diagonale von Matrizen interessiert."


open Nat Matrix BigOperators StdBasisMatrix



    -- around Matrices/level 2: introduce E_ij-version of Matrix.StdBasisMatrix.mul_of_ne,
    -- prove it in one line via mathlib, and use it in level 7.
    -- Matrices/level 3, sum not displayed: already fixed in mathlib


-- -- Not used later on in our proofs, but possibly useful and can be safely
-- -- removed, or given as a hint
-- lemma tmp0 {n : ℕ} {i : Fin n} :
--     E i i = stdBasisMatrix i i ((1 : Mat[n,n][ℝ]) i i) := by
--   rw [one_apply]
--   unfold E
--   simp?

/---/
TheoremDoc Matrix.ebasis_diag_sum_eq_one as "ebasis_diag_sum_eq_one" in "Matrix"

Statement Matrix.ebasis_diag_sum_eq_one {n : ℕ} : ∑ i : Fin n, E i i = 1 := by
  rw [matrix_eq_sum_ebasis 1] -- Lvl 3
  Hint "**Du**: Ich denke, die beiden Summen sind identisch, weil jeder Summand identisch ist.
  Denkst du das funktioniert ähnlich wie mit den Funktionen, da bei dieser Bibliothek?

  **Robo**: Die beiden Taktiken `congr` und `ext` könnten dir hir tatsächlich helfen."
  congr
  ext i r s
  Hint "**Du**: Oh, jetzt habe ich nicht nur den Summationsindex, sondern auch noch die beiden
  Indices `{r},{s}` der Matrizen eingeführt. Aber das sollte passen. Nur… die verbeleibende Summe
  ist ja überall Null aussert beim Index `{i}`.

  **Robo**: Das ist nicht so schön, aber mit `rw [← Finset.sum_subset (Finset.subset_univ {i})]`
  könntest du diese so umschreiben, dass die Summe nur über dem Singleton `\{{i}}` läuft."
  -- have h : {i} ⊆ (Finset.univ : Fin n) := Finset.subset_univ {i}
  rw [← Finset.sum_subset (Finset.subset_univ {i})]
  · Hint "**Du**: Danke, das hilft! Dieser Schritt sollte einfach sein: Eine Summe über ein Element,
    bei diesem ist `1 i i` wieder Eins, und `1 • _` vereinfacht sich auch!"
    Hint (hidden := true) "**Robo**: `simp` klingt wirklich nach einer guten Idee."
    simp
  · intro x h₁ h₂
    clear h₁ -- not needed
    Hint "**Du**: Aber was mache ich hier? `{h₂}` sagt ja mehr oder weniger dass `i ≠ x` ist.

    **Robo**: Ja, aber nicht ganz. Führ das doch mit `have h₃ : i ≠ x` ein und zeig das kurz!"
    -- TODO: There are other way to get `i ≠ x`!
    Branch
      have h₃ : x ≠ i
      Hint "**Robo**: Umgekehrt ist es nütlicher, da
      `1 i x` als `if i = x then _ else _` definiert ist!

      **Du**: Du hast recht, dann braucht man dann `i = x` oder `i ≠ x`. Lass mich das ändern."
    have h₃ : i ≠ x
    · Hint "**Du**: Als erstes würde ich mal schauen, ob sich `{h₂}` vereinfacht."
      simp at h₂
      Hint "**Du**: Hmm, jetzt ist das erstmal verdreht.

      **Robo**: Das war `symm`, das ist uns schon mal begegnet.

      **Du**: Ah ja, da bei diesem wilden Typen mit seinen Förderbändern."
      symm
      assumption
    Branch
      simp [h₃]
    Hint "**Du**: Wie setze ich denn jetzt eigentlich die Definition für `1 {i} {x}` ein?

    **Robo**: `Matrix.one_apply`!"
    rw [Matrix.one_apply]
    Hint "**Robo**: und da das falsch ist kannst du `rw` und `if_neg` weiterkommen."
    rw [if_neg h₃]
    simp

NewTheorem Matrix.one_apply

TheoremTab "Matrix"
