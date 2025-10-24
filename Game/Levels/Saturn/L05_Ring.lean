import Game.Metadata

World "Saturn"
Level 5

Title ""

-- Introduction ""
Introduction "Intro Saturn L05"

/- a well-known polyonmial sums-of-squares formula --/

namespace MvPolynomial
Statement (A B :  MvPolynomial (Fin 4) ℝ) (hA : A = (X 0)*(X 3) - (X 1)*(X 2)) (hB : B = (X 0)*(X 2) + (X 1)*(X 3)) :
  ((X 0)^2 + (X 1)^2) * ((X 2)^2 + (X 3)^2) = A^2 + B^2  := by
  rw [hA, hB]
  ring

/-  older version:
     very artificial & more complicated
     was meant as preparation for Boss level of Babylon, but that level has become simpler

Statement (z a b : ℤ) (h2b : 2*b = 100) (hb2 : b^2 = -100*a - a^2) (h :  z = (a + b)^2) : z = 0 := by
  Hint (hidden := true) "
    **Robo**:  Ich vermute, hier wirst du doch das ein oder andere Lemma brauchen, das wir gerade gesehen haben.
    Du könntest zum Beispiel mit `rw [add_pow_two] at h` anfangen.
  "
  rw [add_pow_two] at h -- or ring
  Hint (hidden := true) "
    **Robo*: Jetzt willst du in `h` aus `(2*a)*o` den Ausdruck `a*(2*o)` machen, damit du `h2o`- benutzen kannst, nicht wahr?
    Vielleicht machst du erst einmal mit `mul_comm` aus `2*a` den Ausdruck `a*2`.
  "
  Branch
    rw [mul_comm] at h
    Hint "
      **Du**: Das war nicht, was ich wollte.

      **Robo**:  Nein. In diesem Fall musst du wohl genauer sagen, welche beiden Zahlen du vertauschen möchtest:
      `mul_comm 2 a`.
    "
  rw [mul_comm 2 a] at h
  Hint (hidden := true) "
    **Robo**: Und jetzt `mul_assoc`.
  "
  rw [mul_assoc] at h
  rw [h2b] at h
  rw [hb2] at h
  rw [h]
  ring
-/

TheoremTab "+ *"

/-
Conclusion "
  “Bestanden” heißt es kurz und knapp vom anonymen Funker.

  **Robo**: Ich glaube, der Antrieb hat sich jetzt genügend regeniert.
  Nichts wie weg!
"
-/
Conclusion "`CONC` Conclusion Saturn L05"
