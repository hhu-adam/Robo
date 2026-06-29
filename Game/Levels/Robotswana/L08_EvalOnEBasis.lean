import Game.Levels.Robotswana.L07_EBasisZeroOffDiag

World "Robotswana"
Level 8

Title "" -- "Die Summe der Summe der Summe"

/- NOTE

  This level used to introduced an essential lemma for the Boss level L10.
  Now the Boss level has a simpler solution, so strictly speaking this level
  is not needed anymore.  Keeping it here as an additional exercise.
-/

/-
Introduction
"
Ihr findet nochmals einen Hinweis, aber in der Eile verliert ihr die Fährte.
Du bist inzwischen sehr durstig.
Während Robo die nähere Umgebung absucht, setzt du dich erschöpft hin und
starrst unter der warmen Sonne etwas beduselt auf den Pergamentfetzen.
"
-/
Introduction "Intro Robotswana L08"

/-
Conclusion "**Du**: Na endlich.

Robo reicht dir eine Flasche Wasser.

**Du**: Wo hast du die denn auf einmal her?

**Robo**: Trick 17.

**Du**:  Und hast du die Fährte wiedergefunden?

**Robo**:  Ja, komm mit! Da hinten hab ich etwas gesehen."
-/
Conclusion "Conclusion Robotswana L08"

open Nat Matrix Finset

Statement {n : ℕ} {f : Mat[n,n][ℝ] →ₗ[ℝ] ℝ}
    (h₁ : ∀ A B, f (A * B) = f (B * A))
    (A : Mat[n,n][ℝ]) :
    f A = ∑ i : Fin n, (A i i) * f (E i i) := by
  /-
  Hint "**Du**: Was das wohl jetzt soll …?

  Du kritzelst einen bisschen herum.

  $$
  \\begin\{aligned}
    f(A)
    &= f\\left( \\sum_\{i,j} A_\{i,j} \\cdot E_\{i,j} \\right) \\\\ %(new line)
    &= \\sum_\{i,j} A_\{i,j} \\cdot f(E_\{i,j})   \\\\ %(new line)
    &= \\sum_\{i} A_\{i,i} \\cdot f(E_\{i,i})
  \\end\{aligned}
  $$

  **Du**: Ja, so könnte das gehen.  Ich schreibe `A` als Summe von Basismatrizen,
  nutze dann die Linearität, und zuletzt, dass `f` auf den `E i j` mit `i ≠ j` verschwindet.

  Vermutlich sollte ich also als erstes das `A` in `f A` als Summe von Basismatrizen
  schreiben, nicht aber das andere `A` weiter hinten.

  **Robo** (*aus der Ferne*): `nth_rw 1 [ … ]`! Funktioniert wie `rw`."
  -/
  Hint "
  $$
  \\begin\{aligned}
    f(A)
    &= f\\left( \\sum_\{i,j} A_\{i,j} \\cdot E_\{i,j} \\right) \\\\ %(new line)
    &= \\sum_\{i,j} A_\{i,j} \\cdot f(E_\{i,j})   \\\\ %(new line)
    &= \\sum_\{i} A_\{i,i} \\cdot f(E_\{i,i})
  \\end\{aligned}
  $$

  Write `A` as sum of base matrices. Use linearity to make `f` disappear in `E i j` with `i ≠ j`.
  Rewrite first `A` in `f A` as sum of base matrices, but not the later `A`. Try `nth_rw 1 [ ... ]`
  which works like `rw`.
  "
  /-
  Hint (hidden := true) "**Du** (*schreiend*): Was meinst du damit?

  **Robo** (*ebenfalls schreiend*): Na, du willst bestimmt `matrix_eq_sum_ebasis A` anwenden, aber mit `nth_rw 1` und nicht mit `rw`.
  `rw [matrix_eq_sum_ebasis A]` würde beide `A`s ersetzen."
  -/
  Hint (hidden := true) "Explain why to use `matrix_eq_sum_ebasis A` with `nth_rw 1` instead of `rw`. `rw [matrix_eq_sum_ebasis A]` replaces both `A`"
  Branch
      rw [matrix_eq_sum_ebasis A]
      -- Hint "**Du**: Hmm, `rw` ist tatsächlich eine schlechte Idee.
      -- Das sieht zu kompliziert aus. Lass es mich doch mit `nth_rw` versuchen."
      Hint "`rw` is a bad idea here. Try `nth_rw`."
  nth_rw 1 [matrix_eq_sum_ebasis A] -- Lvl 3
  -- Hint "**Du** (*in Gedanken*): Jetzt Linearität nutzen… Und ja nicht an Wasser denken…
  --  Auf Babylon gabs genug Wasser… Woran war ich nochmals?"
  Hint "`IN_HINT 1` Use linearity"
  -- Hint "**Robo** (*von irgendwo*): Das klingt nach `map_sum`.  Glaub nicht, dass wir
  -- das auf Babylon gesehen haben, das fantasierst du. Aber `simp` kennt dieses Lemma bestimmt."
  Hint "Try `map_sum` via `simp`"
  Branch
    simp
  rw [map_sum] -- simp knows this
  -- Hint "**Du**: Ah ja, im Zweifelsfall vereinfachen."
  Hint "Simplify"
  simp
  /-
  Hint "**Robo**: Wie weit bist du jetzt?

  **Du**: Ich muss noch irgendwie einbringen, dass `f` auf den `E i j` mit `i≠j` verschwindet.

  **Robo**: Mach doch folgenden Zwischenschritt:

  `trans ∑ i, ∑ j, if i = j then (A i j) * f (E i j) else 0`"
  -/
  Hint "Use disappearing `f` in `E i j` with `i≠j`. Try `trans ∑ i, ∑ j, if i = j then (A i j) * f (E i j) else 0`"
  trans ∑ i, ∑ j, if i = j then (A i j) * f (E i j) else 0
  -- · Hint "**Robo**: Summe gleich Summe … das gehst du mit `apply congr_arg`, `ext` an."
  · Hint "Try using `apply congr_arg` and `ext`"
    apply congr_arg
    ext i
    -- Hint (hidden := true) "**Du**: Vielleicht gleich nocheinmal?"
    Hint (hidden := true) "Try again"
    apply congr_arg
    ext j
    -- Hint "**Du**: Und jetzt Fallunterscheidung zu `{i} = {j}`…"
    Hint "Prove by cases for `{i} = {j}`"
    -- Hint (hidden := true) "**Robo**: `by_cases` war das, genau!"
    Hint "Employ `by_cases`"
    by_cases h₂ : i = j
    -- · Hint "**Robo**: Hier ist `if_pos {h₂}` nützlich."
    · Hint "Try `if_pos {h₂}`."
      rw [if_pos h₂]
    /-
    · Hint "**Robo**: …und hier `if_neg {h₂}`.

      **Du**: Weiß ich doch."
    -/
    · Hint "Here try `if_neg {h₂}`"
      rw [if_neg h₂]
      -- Hint "**Du**: `f (E i j)` ist doch Null, hatten wir doch schon gesehen!"
      Hint "See that `f (E i j)` is zero"
      -- Hint (hidden := true) "**Robo**: Und das hieß `zero_on_offDiag_ebasis`."
      Hint "This was called `zero_on_offDiag_ebasis`"
      rw [zero_on_offDiag_ebasis]
      · simp
      · assumption
      · assumption
  /-
  · Hint "**Du**: Und ich dachte schon das wär's.

    **Robo**: Fast, da ist noch die zweite Hälfte des `trans`-Befehls oben. Diese Hälfte
    ist ganz einfach.
    "
  -/
  · Hint "Solve second half of `trans` operation"
    simp

/-- [Doc.Theorem] map_sum
Linear mapping, or 'additive' mappings in general, can be exchanged with a sum.
-/
TheoremDoc map_sum as "map_sum" in "∑ Π"

TheoremTab "Matrix"
NewTheorem map_sum
