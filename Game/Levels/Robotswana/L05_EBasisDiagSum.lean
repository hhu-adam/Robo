import Game.Levels.Robotswana.L04_MatrixEqSum

World "Robotswana"
Level 5

Title "" -- "Einheitsmatrix"

/-
Introduction
"
**Du**: Zeig mal, was hast du da? Was zur Einheitsmatrix? Passend für unsere Sammlung?

**Robo**: Ja – die `1` ganz rechts ist hier die Einheitsmatrix.
  Ich glaube, du kannst gleich mit `matrix_eq_sum_ebasis` beginnen.

**Du**: Ich frage mich, ob wir noch wichtiges auf dem Platz zurückgelassen haben?

**Robo**: Egal, jetzt sind wir schon ein gutes Stücken weiter. Probier jetzt hier einmal!
"
-/
Introduction "Intro Robotswana L05: `1` indicates unit matrix. Begin with `matrix_eq_sum_ebasis`"

/-
Conclusion "**Du**: Ich habe das Gefühl, wir sind jemandem auf der Spur, der sich für die
die Diagonale von Matrizen interessiert.  Aber ich bekomme langsam Durst!"
-/
Conclusion "`CONC` Conclusion Robotswana L05"

open Nat Matrix

open Finset

    -- around Matrices/level 2: introduce E_ij-version of Matrix.single_mul_single_of_ne,
    -- prove it in one line via mathlib, and use it in level 7.
    -- Matrices/level 3, sum not displayed: already fixed in mathlib


-- -- Not used later on in our proofs, but possibly useful and can be safely
-- -- removed, or given as a hint
-- lemma tmp0 {n : ℕ} {i : Fin n} :
--     E i i = single i i ((1 : Mat[n,n][ℝ]) i i) := by
--   rw [one_apply]
--   unfold E
--   simp?

/---/
TheoremDoc Matrix.ebasis_diag_sum_eq_one as "ebasis_diag_sum_eq_one" in "Matrix"

Statement Matrix.ebasis_diag_sum_eq_one {n : ℕ} : ∑ i : Fin n, E i i = 1 := by
  /-
  Hint (hidden := true) "
    **Robo**:  Wie gesagt, ich denke, du kannst gleich mit `matrix_eq_sum_ebasis` anfangen,
    angewendet auf die Einheitsmatrix `1` rechts vom Gleichheitszeigen.
    Du willst also mit der Gleichung `matrix_eq_sum_ebasis 1` das Beweisziel `r`e`w`riten.
  "
  -/
  Hint (hidden := true) "Try `matrix_eq_sum_ebasis` on `1` with `matrix_eq_sum_ebasis 1` to `r`e`w`rite
  goal."
  Branch
    rw [matrix_eq_sum_single 1]
    -- Hint "**Robo**:  Nein, nicht `matrix_eq_sum_single`, sondern `matrix_eq_sum_ebasis`."
    Hint "Try `matrix_eq_sum_ebasis` not `matrix_eq_sum_single`"
  rw [matrix_eq_sum_ebasis 1] -- Lvl 3
  -- Hint "**Du**: Ich denke, die beiden Summen sind identisch, weil jeder Summand identisch ist."
  Hint "`STORY` explanation of equal sums"
  /-
  Hint (hidden := true) "
    **Robo**:  Dann solltest du vermutlich wieder `sum_congr` anwenden.
  "
  -/
  Hint (hidden := true) "Try `sum_congr`"
  apply sum_congr
  rfl
  intro i hi
  /-
  Hint "**Du**: Und jetzt?

  **Robo**: Mit `funext r s` könntest du dich auf den Eintrag der Matrix an der Stelle $(r,s)$ konzentrieren.
  "
  -/
  Hint "Try `funext r s` to focus on position $(r,s)$."
  funext r s
  /-
  Hint "**Du**: `1` war hier die Einheitsmatrix, richtig?

  **Robo**: Ja.

  **Du**:  Dann ist `1 {i} j` doch Null für alle `j ≠ {i}`.
  Also verschwindet alle Summanden bis auf den Summanden für `j = {i}`.

  **Robo**: Ist das so?   Dann lass mich mal überlegen …
  Kannst du zuerst mal `have h : \{{i}} ⊆ univ` zeigen?"
  -/
  Hint "Explain `1` and values of `1 {i} j` for all `j ≠ {i}` i.e. `j = {i}`. Try `have h : \{{i}} ⊆ univ`"
  have h : {i} ⊆ univ
  · simp
  -- Hint "**Robo**: Sehr gut.  Jetzt kannst du nämlich `sum_subset` anwenden."
  Hint "Now `sum_subset` can be applied"
  rw [← sum_subset h]
  -- · Hint "**Du**: Danke, das hilft! Dieser Schritt sollte einfach sein: Eine Summe über ein Element,
  --  bei diesem ist `1 {i} {i}` wieder Eins, und `1 • _` vereinfacht sich auch!"
  · Hint "Explain simplification of `1 {i} {i}` and `1 • _`"
    -- Hint (hidden := true) "**Robo**: `simp` kann man immer versuchen …"
    Hint (hidden := true) "Try `simp`"
    simp
  · intro x h₁ h₂
    clear h₁ -- not needed
    /-
    Hint "**Du**: Aber was mache ich hier? `{h₂}` sagt ja mehr oder weniger dass `{i} ≠ {x}` ist.

    **Robo**: Ja, aber nicht ganz. Führ das doch mit `have h₃ : {i} ≠ {x}` ein und zeig das kurz!"
    -/
    -- TODO: There are other ways to get `i ≠ x`!
    Hint "Explain that `{h₂}` states `{i} ≠ {x}`. Try `have h₃ : {i} ≠ {x}`"
    Branch
      have h₃ : x ≠ i
      /-
      Hint "**Robo**: Umgekehrt wäre es nützlicher, da
      `1 {i} {x}` als `if {i} = {x} then _ else _` definiert ist!

      **Du**: Du hast recht, ich brauch gleich `{i} = {x}` oder `{i} ≠ {x}`. Lass mich das ändern."
      -/
      Hint "Explain that `1 {i} {x}` is defined as `if {i} = {x} then _ else _` and that either `{i} = {x}` or `{i} ≠ {x}` is needed"
    have h₃ : i ≠ x
    -- · Hint "**Du**: Als erstes würde ich mal schauen, ob sich `{h₂}` vereinfacht."
    · Hint "Try to simplify `{h₂}`."
      simp at h₂
      -- TODO : `tauto` already solves this.
      /-
      Hint "**Du**: Hmm, jetzt ist das erstmal verdreht.

      **Robo**: Erinnere dich an `symm`!

      **Du**: Richtig, das brauchten wir ja schon bei diesem wilden Typen mit seinen Förderbändern."
      -/
      Hint "Try `symm` to fix skewed order"
      symm
      assumption
    Branch
      simp [h₃]
    /-
    Hint "**Du**: Wie setze ich denn jetzt die Definition für `1 {i} {x}` ein?

    **Robo**: `Matrix.one_apply`!"
    -/
    Hint "Apply definition `1 {i} {x}` by `Matrix.one_apply`"
    rw [Matrix.one_apply]
    -- Hint "**Robo**: Und da das falsch ist, kannst du mit `rw` und `if_neg` weiterkommen."
    Hint "Try `rw` and `if_neg`"
    rw [if_neg h₃]
    simp

/---/
TheoremDoc Matrix.one_apply as "one_apply" in "Matrix"

NewTheorem Matrix.one_apply

TheoremTab "Matrix"
