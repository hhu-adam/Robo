import Game.Levels.MatrixTrace.L08_EvalOnEBasis

World "Trace"
Level 9

Title "Trace"

Introduction
"
Während ihr euch anschleicht.

**Du** (**flüsternd**): Weisst du was? Mit all den Spuren, die wir gefunden haben, bin
ich zum Schluss gekommen, dass es gar nicht mehrere solche Wesen gibt, sondern nur eins.

**Robo**: Wie kommst du darauf?

**Du**: Schau, seine Grösse und vorliebe für Kommutatoren, und all die anderen Sachen,
damit kann man doch zeigen, dass es eindeutig identifiziert werden kann!

**Robo**: Das musst du mir genauer erklären.

**Du**: Klar, aber lass uns das da vorne währenddessen beobachten. Und wegen seiner Liebe
zu Diagonalen nenne ich es zwischenzeitlich \"Tracy\"."

Conclusion "

Ihr beobachtet voller Entzücken diese offenbar einzigartige Wesen auf diesem Planeten.

Als ihr näher kommt scheint euch Tracy zu bemerken, aber es scheint dadurch keinesfalls gestört
zu sein.
"

open Nat Matrix BigOperators StdBasisMatrix Finset

/---/
TheoremDoc Matrix.trace_eq as "trace_eq" in "Matrix"

Statement Matrix.trace_eq {n : ℕ} (f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ)
    (h₁ : ∀ A B, f (A * B) = f (B * A)) (h₂ : f 1 = n) :
    trace = f := by
  Hint "**Robo**: Also die Spuren bei unserem Raumschiff, das war sicher Tracy?

    **Du**: Ja, schau. Zwei so Dinger sind identisch wenn sich für äusseren Einflüsse
    komplett identisch verhalten."
  Hint (hidden := true) "
    **Robo**: Also `ext` in mathematischem Jargon!"
  ext A
  Hint "**Du**: Und dann schreibe mal `f A` als Summe von Basiselementen."
  rw [eq_sum_apply_diag_ebasis] -- Lvl 7
  Hint "**Robo**: Ah und den Fall `n = 0` sehe ich sofort!

    **Du**: Wirklich?

    **Robo**: Ja, die Spur einer 0×0-Matrix ist per Definition `0`. Mach mal `rcases n`.

    **Du**: Nicht `induction n`?

    **Robo**: Geht auch, aber wir brauchen die Induktionshypothese nicht."
  rcases n
  · Hint (hidden := true) "**Robo**: Ich hab einfach `simp` ausprobiert und das Betriebsystem
      gibt ein wohliges Schnurren zurück. Probier es mal."
    simp
  · Hint "**Du**: Wir hatten doch eben festgestellt, dass `f (E i i) = 1` gilt!

      **Robo**: Nachschlagen kann ich gut! Das war `one_on_diag_ebasis`."
    Hint (hidden := true) "**Robo**: Denk daran, unter einer Summe must du `simp_rw` verwenden,
      `rw` kann das nicht.

      **Du**: Ah, und die expliziten Argumente `h₁` und `h₂` sollte ich wohl auch noch angeben?"
    simp_rw [one_on_diag_ebasis h₁ h₂] -- Lvl 8
    Hint (hidden := true) "**Du** `_ * 1` ist `simp`, oder?"
    simp
    Hint "**Robo**: Die beiden sind per Definition gleich!"
    rfl
  Hint "**Du**: Wo kommt denn das Goal her?

  **Robo**: Ganz am Anfang bei `rw [eq_sum_apply_diag_ebasis]` hast du vermutlich dieses Argument
  ausgelassen, jetzt kannst du es noch nachholen."
  assumption

/--

Nicht genau definiert als, aber per Definition äquivalent zu:
`trace A = ∑ i, A i i`.

Mathlib benutzt den Term `diag A i` auf den wir hier nicht genauer eingehen.

-/
DefinitionDoc Matrix.trace as "trace"

NewDefinition Matrix.trace
TheoremTab "Matrix"
