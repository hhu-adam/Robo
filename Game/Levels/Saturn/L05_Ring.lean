import Game.Metadata

World "Saturn"
Level 2

Title ""

Introduction "Der nächste Funktspruch"

Statement (w a o : ℤ) (h2o : 2*o = 100) (ho2 : o^2 = -100*a - a^2) (h :  w = (a + o)^2) : w = 0 := by
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
  rw [h2o] at h
  rw [ho2] at h
  rw [h]
  ring

Conclusion "
  “Bestanden” heißt es kurz und knapp von anonymen Funker.

  **Robo**: Ich glaube, der Antrieb hat sich jetzt genügend regeniert.
  Nichts wie weg!
"
