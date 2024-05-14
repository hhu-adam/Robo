import Game.Metadata
import Game.Levels.Cantor.L04_IsFixedPt_not

World "Cantor"
Level 6

Title "Fixpunkte"

Introduction
"
**Cantor**: Zum Beispiel bei ungeraden Funktionen. Da sind die Fixpunkte symmetrisch.

**Du** (*flüsternd zu Robo*): Das hat jetzt wirklich nichts mehr mit der ursprünglichen
Frage zu tun

**Robo** (*leise*): Na komm schon, wir kommen bestimmt gleich dazu.
"

open Function Set Setoid

Statement {f : ℝ → ℝ} (h_odd : ∀ x, f (-x) = - f x) :
    IsFixedPt f x ↔ IsFixedPt f (- x) := by
  constructor
  · intro h
    unfold IsFixedPt
    rw [h_odd x]
    rw [h]
  · intro h
    unfold IsFixedPt at h
    rw [h_odd x] at h
    rw [neg_inj] at h
    assumption

NewTheorem neg_inj
TheoremTab "Function"
