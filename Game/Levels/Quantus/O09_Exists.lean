import Game.Metadata

World "Quantus"
Level 9

Title ""

/-
Introduction
"
Sofort taucht das nächste Blatt auf. Anscheinend hatten sie sich auf einen Kompromiss geeinigt.
"
-/
Introduction "Intro Quantus O09"

Statement (n : ℕ) (h : Odd n) : Odd (n ^ 2) := by
  /-
  Hint (hidden := true) "
    **Robo**: mit `choose r hr using h` kannst du wieder
    das `r` nehmen, das laut Annahme existieren muss.

    **Robo**: Oder aber, du fängst mit `unfold Odd at *` an."
  -/
  Hint (hidden := true) "Try `choose r hr using h` | `unfold Odd at *`"
  Branch
    unfold Odd
    -- Hint "**Robo**: Mit `unfold Odd at *` öffnest du alle Definitionen von `Odd`."
    Hint "Try `unfold Odd at *` to open defintions of `Odd`"
    unfold Odd at *
  Branch
    unfold Odd at *
    /-
    Hint (hidden := true) "
      **Robo**: mit `choose r hr⟩ using h` kannst du wieder
      das `r` nehmen, das laut Annahme existieren muss."
    -/
    Hint (hidden := true) "Take `r` by `choose r hr⟩ using h`"
    choose r hr using h
    /-
    Hint "
      **Robo**: Ich hab noch einen Trick auf Lager:
      Wenn du jetzt noch nicht weißt, welche Zahl du einsetzen musst, könntest
      du schon jetzt mit `rw [{hr}]` weitermachen …"
    -/
    Hint "Try `rw [{hr}]`"
    Branch
      rw [hr]
      /-
      Hint "
        **Robo**: Wenn du jetzt `ring` brauchst, dann schreibt es einfach alles in
        Normalform um, das hilft beim Vergleichen."
      -/
      Hint "Try `ring`"
      ring
    use 2 * (r + r ^ 2)
    ring
  choose r hr using h
  /-
  Hint "
    **Robo**: Ich hab noch einen Trick auf Lager:
    Wenn du jetzt noch nicht weißt, welche Zahl du einsetzen musst, könntest
    Du schon jetzt mit `rw [{hr}]` weitermachen…"
  -/
  Hint "Try `rw [{hr}]`"
  Branch
    rw [hr]
    /-
    Hint "
      **Robo**: Wenn du jetzt `ring` brauchst, dann schreibt es einfach alles in
      Normalform um, das hilft beim Vergleichen."
    -/
    Hint "Try `ring`"
    ring
  use 2 * (r + r ^ 2)
  rw [hr]
  ring

-- Conclusion "Applaus!"
Conclusion "Conclusion Quantus O09"

-- TODO: THis level would be a good example where a `Hint (defeq := true)` would be desirable
-- in order to reduce the number of hints that are duplicated.
