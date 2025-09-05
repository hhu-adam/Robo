import Game.Levels.Robotswana.L09_EvalOnEBasis

World "Robotswana"
Level 10

Title "" -- "Trace"

Introduction
"
Ihr schleicht euch langsam an.

**Du** (**flüsternd**): Ich glaube, du hattest Recht.  Diese Zettel sind eine Art Steckbrief!
Und sie beschreiben dieses Wesen hier eindeutig!

**Robo**: Wie meinst du das?

**Du**: Schau doch, seine Größe, seine Vorliebe für Kommutatoren, und all die anderen Sachen,
damit kann es eindeutig identifiziert werden!

**Robo**: Das musst du mir genauer erklären.

**Du**:  Ich versuch's mal. Gibt es in Leansch einen Namen für die Spur?

**Robo**: Ja klar, die heißt natürlich `trace`.  Manche Formalosophen nennen sie auch liebevoll Tracy.

Du nimmst einen der Pergamentfetzen und schreibst auf die Rückseite.
"

Conclusion "
**Robo**: Tatsache. Du hattest Recht.

Ihr beobachtet voller Entzücken dieses offenbar einzigartige Wesen auf diesem Planeten.

Als ihr näher kommt, scheint euch Tracy zu bemerken.  Aber es scheint dadurch keinesfalls gestört
zu sein.
"

open Nat Matrix Finset

/---/
TheoremDoc Matrix.trace_eq as "trace_eq" in "Matrix"

Statement Matrix.trace_eq {n : ℕ} (f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ)
    (h₁ : ∀ A B, f (A * B) = f (B * A)) (h₂ : f 1 = n) :
    trace = f := by
  Hint "**Du**:  Hier sind noch einmal alle Eigenschaften zusammengefasst.

    **Robo**:  Und du behauptest, nur Tracy hat diese Eigenschaften?

    **Du**: Ja.  Ich glaube, das ist so.  Jedes `f`, dass diese Eigenschaften hat, verhält sich auf allen Matrizen genauso wie Tracy.  Und deshalb *ist* es Tracy!"
  Hint (hidden := true) "
    **Robo**: `ext`!"
  ext A
  Hint "**Du**: Und jetzt schreiben wir `f {A}` als Summe von Basiselementen."
  rw [eq_sum_apply_diag_ebasis] -- Lvl 8
  Hint (hidden := true) "
      **Du**: Wir hatten doch eben festgestellt, dass `f (E i i) = 1` gilt!

      **Robo**: Nachschlagen kann ich gut! Das war `one_on_diag_ebasis`."
  simp [one_on_diag_ebasis h₁ h₂] -- Lvl 9
  Hint (hidden := true) "**Robo**: Die beiden Seiten sind per Definition gleich!"
  rfl
  Hint "**Du**: Wo kommt denn dieses Beweisziel jetzt noch her?

  **Robo**: Ganz am Anfang bei `rw [eq_sum_apply_diag_ebasis]` hast du vermutlich dieses Argument
  ausgelassen.  Jetzt kannst du es noch nachholen."
  assumption

NewDefinition Matrix.trace
TheoremTab "Matrix"
