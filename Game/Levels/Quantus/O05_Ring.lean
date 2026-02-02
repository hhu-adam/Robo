import Game.Metadata

World "Quantus"
Level 5

Title "" -- "Natürliche Zahlen"

-- Introduction ""
Introduction "Intro Quantus O05"

Statement
    (x y z : ℕ) (h : x = 2 * y + 1) (g : z = 3 * y + 1): x ^ 2 = 4 * y ^ 2 + z + y := by
  /-
  Hint "
    **Du**: Ich vermute, wenn ich zuerst alles so umschreibe, dass
    das Beweisziel nur noch rechnen und umsortieren zu beweisen ist, erledigt `ring` den Rest!

    **Robo**: Genau. Und noch ein Trick: Zwei Schritte `rw [h₁]` und `rw [h₂]` kann man zu
    einem einzigen Schritt zusammenfassen: `rw [h₁, h₂]`."
  -/
  Hint "Rewrite statement. Try `rw [h₁, h₂]`, `ring`"
  rw [h, g]
  ring


-- Conclusion ""
Conclusion "Conclusion Quantus O05"
