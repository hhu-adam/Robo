import Game.Levels.MatrixTrace.L06_EBasisZeroOffDiag

--import Game.StructInstWithHoles

World "Trace"
Level 7

Title "Kommutator"

Introduction
"
Ihr findet nochmals einen Hinweis, aber in der Eile verliert ihr die Fährte.

Während Robo die nähere Umgebung absucht, setzt du dich etwas erschöpft hin und starrst
unter der warmen Sonne etwas bedusselt auf das letzte Pergament.
"

Conclusion "**Du**: Danke für das Wasser, Robo! Hast du eigentlich die Fährte wiedergefunden?

**Robo**: Komm mal mit, da hinten hab ich auf jeden Fall etwas gesehen."

open Nat Matrix BigOperators StdBasisMatrix Finset

/---/
TheoremDoc Matrix.eq_sum_apply_diag_ebasis as "eq_sum_apply_diag_ebasis" in "Matrix"

Statement Matrix.eq_sum_apply_diag_ebasis {n : ℕ} {f : Mat[n,n][ℝ] →ₗ[ℝ] ℝ}
    (h₁ : ∀ A B, f (A * B) = f (B * A))
    (A : Mat[n,n][ℝ]) :
    f A = ∑ i : Fin n, (A i i) * f (E i i) := by
  Hint "**Du**: Ich versteh einfach nicht was es von uns will! Aber bleibt wohl nichts
  anderes übrig als das hier mal anzuschauen…

  **Du** (*brummelnd*): Ich glaube ich möchte das `A` in `f A`, als Summe von Basismatrizen
  schreiben, nicht aber
  das andere `A` weiter hinten.

  Von hinter einem Grassbüschel hörst du den unterstützenden Ruf

  **Robo**: `nth_rw 1 [ ... ]`! Funktioniert wie `rw`."
  Hint (hidden := true) "**Du** (*schreiend*): Was meinst du damit?

  **Robo** (*ebenfalls schreiend*): Na das Lemma ist `matrix_eq_sum_ebasis A` und `nth_rw 1` sagt,
  dass du nur das erste `A` ersetzen willst. `rw` würde beide ersetzen."
  Branch
      rw [matrix_eq_sum_ebasis A]
      Hint "**Du**: Hmm ne, vielleicht ist `rw` doch eine schlechte Idee, das sieht zu
      kompliziert aus. Lass mich es doch mit `nth_rw` versuchen."
  nth_rw 1 [matrix_eq_sum_ebasis A] -- Lvl 3
  Hint "**Du** (*in Gedanken*): Jetzt die Funktion in die Summe rein… Und ja nicht an Wasser denken…
    Aber Wasser hatte es doch auf Babylon… Woran war ich nochmals?"
  Hint "**Robo** (*von irgendwo*): Das klingt nach `map_sum`, aber das hatten wir
  auf Babylon nicht gesehen, da fantasierst du. Aber `simp` kennt dieses Lemma sonst auch."
  Branch
    simp
  rw [map_sum] -- simp knows this
  Hint "**Du**: Ah ja, im Zweifelsfall vereinfachen."
  simp
  Hint "**Du**: Die Summe der Summe der Summe der…

  **Robo*: Hey, woran bist du eigentlich?

  **Du**: Keine Ahnung!

  **Robo**: Mach doch folgenden Zwischenschritt:

  `trans ∑ i, ∑ j, if i = j then (A i j) * f (E i j) else 0`"
  trans ∑ i, ∑ j, if i = j then (A i j) * f (E i j) else 0
  · Hint "**Du**: Summe gleich Summe, `congr`-`ext` macht da der Dumme."
    congr
    ext i
    Hint (hidden := true) "**Robo**: Vielleicht gleich nocheinmal?"
    congr
    ext j
    Hint "Robo reicht dir eine Flasche Wasser. Keine Ahnung wo er die her hatte.

    **Du**: Ah langsam seh ich es wieder klarer. Fall Unterscheidung auf `i = j` ist angesagt!"
    Hint (hidden := true) "**Robo**: `by_cases` war das, genau!"
    by_cases h₂ : i = j
    · Hint "**Robo**: Hier ist `if_pos {h₂}` nützlich."
      rw [if_pos h₂]
    · Hint "**Robo**: …und hier `if_neg {h₂}`.

      **Du**: Kenn ich doch noch."
      rw [if_neg h₂]
      Hint "**Du**: `f (E i j)` ist doch Null, das war doch vorhin so!"
      Hint (hidden := true) "**Robo**: Und das hiess `zero_on_offDiag_ebasis`."
      rw [zero_on_offDiag_ebasis]
      · simp
      · assumption
      · assumption
  · Hint "**Du**: Und ich dachte schon das wär's.

    **Robo**: Fast, da ist noch die zweite Hälfte des `trans`-Befehls oben. Diese Hälfte
    ist aber nur vereinfachen.
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
