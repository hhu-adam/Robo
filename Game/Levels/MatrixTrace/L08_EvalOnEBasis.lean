import Game.Levels.MatrixTrace.L07_EBasisZeroOffDiag

--import Game.StructInstWithHoles

World "Trace"
Level 8

Title "Die Summe der Summe der Summe"

Introduction
"
Ihr findet nochmals einen Hinweis, aber in der Eile verliert ihr die Fährte.
Du bist inzwischen sehr durstig.  
Während Robo die nähere Umgebung absucht, setzt du dich erschöpft hin und
starrst unter der warmen Sonne etwas beduselt auf den Pergamentfetzen.
"

Conclusion "**Du**: Na endlich.  

Robo reicht dir eine Flasche Wasser.

**Du**: Wo hast du die denn auf einmal her? 

**Robo**: Trick 17.

**Du**:  Und hast du die Fährte wiedergefunden?

**Robo**:  Ja, komm mit! Da hinten hab ich etwas gesehen."

open Nat Matrix BigOperators StdBasisMatrix Finset

/---/
TheoremDoc Matrix.eq_sum_apply_diag_ebasis as "eq_sum_apply_diag_ebasis" in "Matrix"

Statement Matrix.eq_sum_apply_diag_ebasis {n : ℕ} {f : Mat[n,n][ℝ] →ₗ[ℝ] ℝ}
    (h₁ : ∀ A B, f (A * B) = f (B * A))
    (A : Mat[n,n][ℝ]) :
    f A = ∑ i : Fin n, (A i i) * f (E i i) := by
  Hint "**Du**: Was das wohl jetzt soll …?
  
  Du kritzelst einen bisschen herum.

  $$
  \\begin\{aligned}
    f(A) 
    &= f\\left( \\sum_\{i,j} A_\{i,j} ⬝ E_\{i,j} \\right) \\\\
    &= \\sum_\{i,j} A_\{i,j} ⬝ f(E_\{i,j})   \\\\
    &= \\sum_\{i,j} A_\{i,i} ⬝ f(E_\{i,i}) 
  \\end\{aligned}
  $$

  **Du**: Ja, so könnte das gehen.  Ich schreibe `A` als Summe von Basismatrizen,
  nutze dann die Linearität, und zuletzt, dass `f` auf den `E i j` mit `i ≠ j` verschwindet.

  Vermutlich sollte ich also als erstes das `A` in `f A` als Summe von Basismatrizen
  schreiben, nicht aber das andere `A` weiter hinten.   

  **Robo** (*aus der Ferne*): `nth_rw 1 [ ... ]`! Funktioniert wie `rw`."
  Hint (hidden := true) "**Du** (*schreiend*): Was meinst du damit?

  **Robo** (*ebenfalls schreiend*): Na, du willst bestimmt `matrix_eq_sum_ebasis A` anwenden, aber mit `nth_rw 1` und nicht mit `rw`.
  `rw [matrix_eq_sum_ebasis A]` würde beide `A`s ersetzen."
  Branch
      rw [matrix_eq_sum_ebasis A]
      Hint "**Du**: Hmm, `rw` ist tatsächlich eine schlechte Idee. 
      Das sieht zu kompliziert aus. Lass es mich doch mit `nth_rw` versuchen."
  nth_rw 1 [matrix_eq_sum_ebasis A] -- Lvl 3
  Hint "**Du** (*in Gedanken*): Jetzt Linearität nutzen… Und ja nicht an Wasser denken…
    Auf Babylon gabs genug Wasser… Woran war ich nochmals?"
  Hint "**Robo** (*von irgendwo*): Das klingt nach `map_sum`.  Glaub nicht, dass wir
  das auf Babylon gesehen haben, das fantasierst du. Aber `simp` kennt dieses Lemma bestimmt."
  Branch
    simp
  rw [map_sum] -- simp knows this
  Hint "**Du**: Ah ja, im Zweifelsfall vereinfachen."
  simp
  Hint "**Robo*: Wie weit bist du jetzt?

  **Du**: Ich muss noch irgendwie einbringen, dass `f` auf den `E i j` mit `i≠j` verschwindet.

  **Robo**: Mach doch folgenden Zwischenschritt:

  `trans ∑ i, ∑ j, if i = j then (A i j) * f (E i j) else 0`"
  trans ∑ i, ∑ j, if i = j then (A i j) * f (E i j) else 0
  · Hint "**Du**: Summe gleich Summe, `congr`-`ext` macht da der Dumme."
    congr
    ext i
    Hint (hidden := true) "**Robo**: Vielleicht gleich nocheinmal?"
    congr
    ext j
    Hint "**Du**: Und jetzt Fallunterscheidung zu `{i} = {j}`…"
    Hint (hidden := true) "**Robo**: `by_cases` war das, genau!"
    by_cases h₂ : i = j
    · Hint "**Robo**: Hier ist `if_pos {h₂}` nützlich."
      rw [if_pos h₂]
    · Hint "**Robo**: …und hier `if_neg {h₂}`.

      **Du**: Weiß ich doch."
      rw [if_neg h₂]
      Hint "**Du**: `f (E i j)` ist doch Null, hatten wir doch schon gesehen!"
      Hint (hidden := true) "**Robo**: Und das hieß `zero_on_offDiag_ebasis`."
      rw [zero_on_offDiag_ebasis]
      · simp
      · assumption
      · assumption
  · Hint "**Du**: Und ich dachte schon das wär's.

    **Robo**: Fast, da ist noch die zweite Hälfte des `trans`-Befehls oben. Diese Hälfte
    ist ganz einfach.
    "
    simp

-- TODO: Where to introduce it? It is for additive `f : A →+ B`, so Babylon might not be ideal
/--
Lineare Abbildungen (oder genereller "additive" Abbildungen) kann man mit einer
Summe vertauschen.
-/
TheoremDoc map_sum as "map_sum" in "Sum"

TheoremTab "Matrix"
NewTheorem map_sum
