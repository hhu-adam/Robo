import Game.Metadata

World "Saturn"
Level 3

Title ""

Introduction "Noch ein Funkspruch."


Statement (a b c: ℕ) : a * b * c = a * (b * c) := by
  ring

Conclusion "
  Wieder ein 👍.

  **Du**: Und wie heißt diese tolle Gleichung?
  Langsam wird das ein bisschen langweilig …

  **Robo**: Sie heißt `mul_assoc`.
  Ja, hoffen wir, dass der volle Antrieb bald wieder da ist.
"

NewTactic ring

/---/
TheoremDoc mul_assoc as "mul_assoc" in "Ring"

NewTheorem mul_assoc
DisabledTheorem mul_assoc
