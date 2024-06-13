import Game.Levels.MatrixTrace.L04_MatrixEqSum

World "Trace"
Level 5

Title "Einheitsmatrix"

Introduction
"
**Du**: Zeig mal, was hast du da? Was zur Einheitsmatrix? Passend für unsere Sammlung?

**Robo**: Ja, schau. Ich glaube, hier kannst Du gleich mit `matrix_eq_sum_ebasis` beginnen.

**Du**: Ich frage mich, ob wir noch wichtiges auf dem Platz zurückgelassen haben?

**Robo**: Egal, jetzt sind wir schon ein gutes Stücken weiter. Probier jetzt hier einmal!
"

Conclusion "**Du**: Ich habe das Gefühl, wir sind jemandem auf der Spur, der sich für die
die Diagonale von Matrizen interessiert.  Aber ich bekomme langsam Durst!"


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

  **Robo**: Die beiden Taktiken `congr` und `ext` könnten dir hier tatsächlich helfen.

  *(von oben)*: Wurde noch nicht erklärt, aber zukünftig werden `ext` und
  `congr` schon früher eingeführt."
  congr -- TODO: Modify story
  ext i r s
  Hint "**Du**: Oh, jetzt habe ich nicht nur den Summationsindex, sondern auch noch die beiden
  Indices `{r},{s}` der Matrizen eingeführt. Aber das sollte passen. Nur… die verbleibende Summe
  ist ja überall Null außer beim Index `{i}`.

  **Robo**: Ist das so?  Lass mich mal suchen…  Nicht schön, sollte aber funktionieren:  mit `rw [← Finset.sum_subset (Finset.subset_univ \{{i}})]`
  solltest du die Summe so umschreiben können, dass sie nur über dem Singleton `\{{i}}` läuft."
  -- have h : {i} ⊆ (Finset.univ : Fin n) := Finset.subset_univ {i}
  rw [← Finset.sum_subset (Finset.subset_univ {i})] -- TODO: better hint once lemmas are introduced
  · Hint "**Du**: Danke, das hilft! Dieser Schritt sollte einfach sein: Eine Summe über ein Element,
    bei diesem ist `1 i i` wieder Eins, und `1 • _` vereinfacht sich auch!"
    Hint (hidden := true) "**Robo**: `simp` klingt wirklich nach einer guten Idee."
    simp
  · intro x h₁ h₂
    clear h₁ -- not needed
    Hint "**Du**: Aber was mache ich hier? `{h₂}` sagt ja mehr oder weniger dass `i ≠ x` ist.

    **Robo**: Ja, aber nicht ganz. Führ das doch mit `have h₃ : i ≠ x` ein und zeig das kurz!"
    -- TODO: There are other ways to get `i ≠ x`!
    Branch
      have h₃ : x ≠ i
      Hint "**Robo**: Umgekehrt wäre es nützlicher, da
      `1 i x` als `if i = x then _ else _` definiert ist!

      **Du**: Du hast recht, ich brauch gleich `i = x` oder `i ≠ x`. Lass mich das ändern."
    have h₃ : i ≠ x
    · Hint "**Du**: Als erstes würde ich mal schauen, ob sich `{h₂}` vereinfacht."
      simp at h₂
      Hint "**Du**: Hmm, jetzt ist das erstmal verdreht.

      **Robo**: Erinnere dich an `symm`!

      **Du**: Richtig, das brauchten wir ja schon bei diesem wilden Typen mit seinen Förderbändern."
      symm
      assumption
    Branch
      simp [h₃]
    Hint "**Du**: Wie setze ich denn jetzt die Definition für `1 {i} {x}` ein?

    **Robo**: `Matrix.one_apply`!"
    rw [Matrix.one_apply]
    Hint "**Robo**: Und da das falsch ist, kannst du mit `rw` und `if_neg` weiterkommen."
    rw [if_neg h₃]
    simp

-- TODO: Introduce in other planet
/-- Dieses Theorem sollte eigentlich woanders eingeführt werden -/
TheoremDoc Finset.sum_subset as "Finset.sum_subset" in "Finset"
/-- Dieses Theorem sollte eigentlich woanders eingeführt werden -/
TheoremDoc Finset.subset_univ as "Finset.subset_univ" in "Finset"
/-- Zwei Funktionen sind gleich, wenn sie auf allen Elementen gleich sind.

Wenn das Goal `f = g` ist, kann man mit `ext i`, ein Element `i` einführen, und dann zeigen,
dass `f i = g i` ist.

`ext` versucht, so viele Indices einzufügen wie möglich `funext i` führt nur den spezifizierten ein.
-/
TacticDoc ext
/-- `congr` versucht, eine Gleichung `_ = _` auf eine Gleichung von Untertermen zu reduzieren. Zum
Beispiel ein Goal der Form `f a = f b` wird durch `congr` zu `a = b` reduziert. -/
TacticDoc congr


NewTheorem Matrix.one_apply Finset.sum_subset Finset.subset_univ

TheoremTab "Matrix"
