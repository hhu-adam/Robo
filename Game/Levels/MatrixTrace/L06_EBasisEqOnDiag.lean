import Game.Levels.MatrixTrace.L05_EBasisDiagSum

World "Trace"
Level 6

Title "Ein nihilierter Kommutator"

-- TODO: Intro & geschichte
Introduction
"
Der Spur folgend kommt ihr an einem großen Baum. Im Schatten findet ihr ein regloses Etwas:

$$
[A, B] = AB - BA
$$

**Robo**:  Ach ja, ein Kommutator!

**Du**: Der sieht aber ziemlich nihiliert aus.  Ich glaube, der ist verdurstet.

**Robo**: Und schau, hier ist noch was in den Baum gekritzelt.
"

Conclusion "
**Robo**: Ich glaube, die Annahme, dass Kommutatoren nihiliert werden, nehmen wir jetzt erst
einmal mit.

**Du**: Schön.  Sagte ich bereits, dass ich langsam Durst habe?
"

open Nat Matrix BigOperators

/---/
TheoremDoc Matrix.eq_on_diag_ebasis as "eq_on_diag_ebasis" in "Matrix"

Statement Matrix.eq_on_diag_ebasis {n : ℕ} {f : Mat[n,n][ℝ] →ₗ[ℝ] ℝ}
    (h₁ : ∀ A B, f (A * B) = f (B * A))  :
    ∀ (i j : Fin n), f (E i i) = f (E j j) := by
  Hint "**Du**: Mit anderen Worten: Wenn `f` Kommutatoren nihiliert, dann stimmen seine Werte
  auf allen `E i i` überein. Stimmt das??

  **Robo**: Lass es uns herausfinden!"
  intro i j
  Hint "**Du**: Aber was soll ich denn mit unserer Annahme `{h₁}` anfangen!
  Ich müsste überhaupt erst einmal eine Multiplikation haben.

  **Robo**: Du müsstest ein Matrizenprodukt `A * B` finden, für das  `f (E i i) = f (A * B) = f (E j j)` gilt.
  Dann könnstest du `trans f (A * B)` schreiben, um zwei Beweisziele – `f (E i i) = f (A * B)` und `f (A * B) = f (E j j)` – zu erhalten,
bei denen `{h₁}` vielleicht anwendbar ist."
  Hint (hidden := true) "**Robo**: Hatten wir nicht `E i k = (E i j) * (E j k)` auf einem dieser Zettel?"
  trans f (E i j * E j i)
  · unfold E
    simp
  · Hint (hidden := true) "**Robo**: Hast du das nicht alles gemacht, weil du `{h₁}` brauchen
    wolltest?

    **Du**: Ah ja, stimmt!"
    rw [h₁]
    unfold E
    simp

TheoremTab "Matrix"
