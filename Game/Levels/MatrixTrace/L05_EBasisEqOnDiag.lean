import Game.Levels.MatrixTrace.L04_EBasisDiagSum

World "Trace"
Level 5

Title "Kommutator"

-- TODO: Intro & geschichte
Introduction
"
Der Spur folgend unter einem breiten Baum findet ihr im Schatten ein komisches regloses etwas.

$$
[A, B] = AB - BA
$$

Beim genauen inspizieren stellt Robo fest dass er dieses unter dem Namen Matrizenkommutator kennt.

**Du**: Das sieht ziemlich nihiliert aus.

**Robo**: Und schau hier ist noch was in den Baum gekritzelt.
"

Conclusion "
**Du**: Ich glaube, die Annahme dass unser etwas Kommutatoren nihiliert, nehmen wir jetzt erst
einmal mit.
"

open Nat Matrix BigOperators

/---/
TheoremDoc Matrix.eq_on_diag_ebasis as "eq_on_diag_ebasis" in "Matrix"

Statement Matrix.eq_on_diag_ebasis {n : ℕ} {f : Mat[n,n][ℝ] →ₗ[ℝ] ℝ}
    (h₁ : ∀ A B, f (A * B) = f (B * A))  :
    ∀ (i j : Fin n), f (E i i) = f (E j j) := by
  Hint "**Du**: Also wenn unser etwas Kommutatoren nihiliert, dann sind für es auch die Werte
  aller `E i i` gleich. Stimmt das wohl?

  **Robo**: Lass es uns herausfinden!"
  intro i j
  Hint "**Du**: Was mache ich wohl mit unserer Annahme `{h₁}`, dazu müsste
  ich wohl zuerst eine Multiplikation haben.

  **Robo**: als was möchtest du denn `E i i` darstellen?

  ** Du**: Man könnte `E i i = (E i j) * (E j i)` darstellen, das sollte gehen.

  **Robo**: Dann hab ich das Werkzeug dazu! Schreib `trans f (E i j * E j i)`, dann hast du zwei
  Goals `f (E i i) = f (E i j * E j i) = f (E j j)`, die du dann einzeln zeigen kannst.
  "
  trans f (E i j * E j i)
  · Hint (hidden := true) "**Du**: Diese erste Hälfte ist nur nachrechnen.

    **Robo**: Da `E` ganz konkret definiert ist, kann das `simp` bestimmt."
    unfold E
    simp
  · Hint (hidden := true) "**Robo**: Hast du das nicht alles gemacht, weil du `{h₁}` brauchen
    wolltest?

    **Du**: Ah ja, stimmt!"
    rw [h₁]
    unfold E
    simp

TheoremTab "Matrix"
NewTactic trans
