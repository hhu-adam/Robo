import Game.Levels.Robotswana.L08_EvalOnEBasis

World "Robotswana"
Level 9

Title "" -- "Matrix"

/-
Introduction
"
Keine fünfzig Meter weiter kommt ihr auf eine kleine Anhöhe.
Robo zeigt auf einen Punkt in der Ferne.

**Robo**: Schau mal, da liegt es!

**Du**: Und was *ist* das???

**Robo**:  Weiß nicht.  Aber mein Gefühl sagt mir, diese Zettel sind eine Art Steckbrief.  Schau mal, hier ist noch einer.  Ich glaube, der sagt, wie groß es ist.
"
-/
Introduction "`INTRO` Intro Robotswana L09"

/-
Conclusion "
  **Du**: Okay. Lass uns vorsichtig näher gehen.
"
-/
Conclusion "`CONC` Conclusion Robotswana L09"

open Nat Matrix Finset
-- Finset needs to be opened so that sum_congr is available
-- (not included in solution below, but can be used in alternative solutions)

/---/
TheoremDoc Matrix.one_on_diag_ebasis as "one_on_diag_ebasis" in "Matrix"

-- set_option trace.Meta.synthInstance true in
-- set_option pp.explicit true in

Statement Matrix.one_on_diag_ebasis {n : ℕ} {f : Mat[n, n][ℝ] →ₗ[ℝ] ℝ}
    (h₁ : ∀ A B, f (A * B) = f (B * A)) (h₂ : f 1 = n) :
    ∀ i, f (E i i) = 1 := by
  intro i
  /-
  Hint "
   Du überlegst ein bisschen und kritzelst auf dem Papier herum.  Nach einer Weile:

   **Du**: Ich glaube, ich habe eine Idee! Das `{n}`-fache der Gleichung kann ich mit den vorherigen Resultaten wie folgt nachrechnen:
  $$
    \\begin\{aligned}
    n \\cdot f(E_\{i i})
    &= \\sum_j f(E_\{i i}) \\\\
    &= \\sum_j f(E_\{j j}) \\\\
    &= f(1) \\\\
    &= n
    \\end\{aligned}
  $$

  Der wesentlich Punkt ist, dass wir ja gesehen hatten, dass `f E i i` und `f E j j` für beliebige `i` und `j` gleich sind.  Also sind sie in der Summe austauschbar.

  **Robo**: Mmm.  Du willst jedenfalls zunächst ausnutzen, dass Multiplikation mit `{n}` injektiv ist?
     Hatten wir dazu nicht mal ein Lemma? Mmm …

  Robo überlegt eine Weile.

  **Robo**:  Ich würds mal so versuchen:
     ```
     suffices h : n * f (E i i) = n * 1
     ```
  Und dann weiter mit `mul_eq_mul_left_iff`.
  "
  -/
  Hint "
  `{n}`-th multiplication of the equation can be calculated with the former results as:
  $$
    \\begin\{aligned}
    n \\cdot f(E_\{i i})
    &= \\sum_j f(E_\{i i}) \\\\
    &= \\sum_j f(E_\{j j}) \\\\
    &= f(1) \\\\
    &= n
    \\end\{aligned}
  $$

  Keep in mind that `f E i i` and `f E j j` are equal for arbitrary `i` and `j`. Use fact that
  multiplications with `{n}` are injective. Try
  ```
  suffices h : n * f (E i i) = n * 1
  ```
  and then continue with `mul_eq_mul_left_iff`.
  "
  -- older version used `nat_mul_inj' (n := n)` from here
  -- now using `mul_eq_mul_left_iff`, cf. Prado
  suffices h : n * f (E i i) = n * 1 by
    rw [mul_eq_mul_left_iff] at h
    obtain h | h := h
    /-
    Hint (hidden := true) "
    **Robo**: Ach ja, den Fall `{h} : {n} = 0`
      müssen wir wohl gesondert betrachten.
      Unterscheiden wir die Fälle also mit `obtain {h} | {h} := {h}`
    "
    -/
    Hint (hidden := true) "Observe `{h} : {n} = 0` seperatly. Prove by cases with `obtain {h} | {h} := {h}`"
    · assumption
    -- · Hint  "
    --  **Robo**: Der Pfeil `{h}` ist eine implizite Einbettung von `ℕ` in `ℝ`.
    --  Die entfernst du zum Beispiel mit `simp`."
    · Hint  "`{h}` is an implicid embedding of  `ℕ` in `ℝ`.  Try `simp`"
      simp at h
      /-
      Hint "
      **Robo**:  Und jetzt willst du vermutlich `{h} : {n} = 0` in `{i} : Fin {n}` einsetzen,
      und feststellen, dass die Aussage trivial wird, weil es gar kein `{i}` in `Fin 0` gibt.
      Zum Einsetzen kannst du in diesem Fall `simp [{h}] at {i}` benutzen.
      "
      -/
      Hint "Put `{h} : {n} = 0` into `{i} : Fin {n}` to show triviality because there is no `{i}` in `Fin 0`. Try `simp [{h}] at {i}`"
      simp [h] at i
      /-
      Hint "
      **Robo**: Und jetzt hilft dir vermutlich das Lemma `IsEmpty.false`,
      das für eine leere Menge `M` besagt `∀ (m : M), False`.
      "
      -/
      Hint "Try `IsEmpty.false`. It states for the empty set `M` that `∀ (m : M), False`"
      Branch
        apply IsEmpty.false at i
        contradiction
      by_contra
      apply IsEmpty.false i
  -- Hint "**Robo**:  Na schön.  Jetzt also zur eigentlichen Sache."
  Hint "Story"
  /-
  Hint (hidden := true) "
  **Robo**: Wenn ich dich richtig verstanden haben, willst du jetzt mehrmals `trans` anwenden, als erstes
  `trans ∑ j : Fin {n}, f (E i i)`.
  "
  -/
  Hint (hidden := true) "Try `trans` several times. Start with `trans ∑ j : Fin {n}, f (E i i)`"
  Branch
    rw [←smul_eq_mul, ← LinearMap.map_smul]
    /-
    Hint "**Robo**: Oh, das ist jetzt aber nicht das, was du eben aufgeschrieben hattest.
      Könnte aber auch funktionieren.
      Probier mal `trans {f} (∑ j : Fin {n}, E {i} {i})` als nächsten Schritt.
      "
    -/
    Hint "Try `trans {f} (∑ j : Fin {n}, E {i} {i})`"
    trans f (∑ x : Fin n, E i i)
    /-
    · Hint "**Du**: Genau, jetzt müssen wir für diese erste Gleichheit nur die konstante Summe ausrechnen.

      **Robo**: `simp [E]` kann das sicher komplett vereinfachen." -- TODO: Better hint
    -/
    · Hint "Try `simp [E]`"
      simp [E] -- TODO: This is a bit magical in the sense that `simp; unfold E; simp` seems not to work
    -- · Hint (hidden := true )"**Du**: Als nächstes ziehen wir die Funktion in die Summe rein."
    · Hint (hidden := true ) "Pull function into sum"
      /-
      Hint "**Du**: Und jetzt möchte ich die Gleichung durch einen Zwischenschritt
      `{f} (∑ x, E x x)` zeigen."
      -/
      Hint "Show statement via `{f} (∑ x, E x x)`"
      trans f (∑ x, E x x)
      · Branch
          apply congr_arg
          -- Hint "**Du**: Nein, das ist jetzt mathematisch falsch!"
          Hint "Story"
        /-
        Hint (hidden := true) "**Robo**: Jetzt wieder `congr`-`ext`?

        **Du**: Nein, zuerst, die Funktion in die Summe rein, sonst klappt das nicht."
        -/
        Hint (hidden := true) "Pull function into sum"
        rw [map_sum]
        -- Hint "**Du**: Nochmals!"
        Hint "again"
        rw [map_sum]
        apply congr_arg
        ext j
        -- Hint "**Du**: Und das war ein Resultat, welches wir auf dem Weg gefunden haben."
        Hint "Remind of previous result"
        -- Hint (hidden := true) "**Robo**: `eq_on_diag_ebasis` sagt meine Speicherplatte."
        Hint (hidden := true) "Try `eq_on_diag_ebasis`"
        rw [eq_on_diag_ebasis] -- Lvl 5
        assumption
      -- · Hint (hidden := true) "**Robo**: Das sieht nach `ebasis_diag_sum_eq_one` aus."
      · Hint (hidden := true) "Try `ebasis_diag_sum_eq_one`"
        rw [ebasis_diag_sum_eq_one] -- Lvl 4
        rw [h₂]
        simp
  · trans ∑ j : Fin n, f (E i i)
    · simp
    · trans ∑ j : Fin n, f (E j j )
      · apply congr_arg
        ext
        -- Hint (hidden := true) "**Robo**: Das hatten wir schon gesehen."
        Hint (hidden := true) "Remind of previous result"
        rw [eq_on_diag_ebasis] -- Lvl 5
        assumption
      · trans f 1
        -- · Hint (hidden := true) "**Robo**: Das Resultat, das du hier anwenden wolltest, hieß `eq_sum_apply_diag_ebasis`."
        · Hint (hidden := true) "Try `eq_sum_apply_diag_ebasis`"
          rw [eq_sum_apply_diag_ebasis] -- Lvl 8
          · simp
          · assumption
        -- · Hint (hidden := true) "**Robo**: Probier mal `rw [{h₂}]`."
        · Hint (hidden := true) "Try out `rw [{h₂}]`"
          rw [h₂]
          simp
  -- · simp -- previously needed for `nat_mul_inj'`



-- TODO: Each of the following theorems should ideally be introduced earlier!

/---/
TheoremDoc smul_eq_mul as "smul_eq_mul" in "Matrix"

/---/
TheoremDoc LinearMap.map_smul as "LinearMap.map_smul" in "Matrix"

--  TheoremDoc nat_mul_inj' as "nat_mul_inj'" in "ℕ"

/---/
TheoremDoc Nat.cast_eq_zero as "cast_eq_zero" in "ℕ"

/---/
TheoremDoc IsEmpty.false as "IsEmpty.false" in "Logic"


TheoremTab "Matrix"
NewTheorem smul_eq_mul LinearMap.map_smul Nat.cast_eq_zero IsEmpty.false
--nat_mul_inj'
