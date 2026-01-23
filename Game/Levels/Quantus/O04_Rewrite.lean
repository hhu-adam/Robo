import Game.Metadata

World "Quantus"
Level 4

Title "" -- "Rewrite"

-- Introduction ""
Introduction "Intro Quantus O04"

/--
$$
\begin{aligned}
  a &= b \\ %(new line)
  a + a ^ 2 &= b + 1 \\ %(new line)
  \vdash b + b ^ 2 &= b + 1
\end{aligned}
$$
 -/
Statement (a b : ℕ) (h : a = b) (g : a + a ^ 2 = b + 1) : b + b ^ 2 = b + 1 := by
  /-
  Hint "
    **Du**: Hier muss man, glaube ich, einfach in Annahme `{g}` die
    Variable `{a}` durch `{b}` ersetzen.

    **Robo**: Genau! Das machst du mit `rw [{h}] at {g}`."
  -/
  Hint "Replace `{a}` by `{b}` in `{g}`. Try `rw [{h}] at {g}`"
  rw [h] at g
  -- Hint (hidden := true) "**Robo**: Schau mal durch die Annahmen."
  Hint (hidden := true) "See assumptions"
  assumption

/-
Conclusion
"
**Robo**: Noch ein Trick: Mit `rw [h] at *` kann man gleichzeitig mittels `h` **alle**
Annahmen und das Goal umschreiben.
"
-/

Conclusion "Conclusion Quantus O04"
