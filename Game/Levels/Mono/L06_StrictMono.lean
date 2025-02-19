import Game.Levels.Mono.L05_StrictMono

World "Mono"
Level 6

Title "" -- ""

Introduction "Anscheinend hat jemand bemerkt, dass `StrictMono.injective` vorgesagt war.
Jetzt wollen sie davon auch einen Beweis sehen."

open Set Function

Statement StrictMono.injective {f : ℤ → ℤ}
    (hf : StrictMono f)  : Injective f := by
  Hint (hidden := true) "
    **Robo**: Vieleicht erst einmal ganz klassisch alle Variablen und Annahmen aus `Injective f` einführen?
  "
  intro a b h
  Hint (hidden := true) (strict := true)"
    **Robo**:  Jetzt vielleicht eine Fallunterscheidung.  Erinnerst du dich an `lt_trichotomy`?
  "
  obtain hlt | heq | hgt := lt_trichotomy a b
  · apply hf at hlt
    rw [h] at hlt
    linarith
  · assumption
  · -- proof by symmetry (e.g. `wlog` or `swap`)
    apply hf at hgt
    rw [h] at hgt
    linarith

DisabledTheorem StrictMono.injective
