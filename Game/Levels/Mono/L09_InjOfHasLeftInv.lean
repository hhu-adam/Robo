import Game.Levels.Mono.L08_RightInvOfLeftInv

World "Mono"
Level 9

Title ""

Introduction ""

open Function

/---/
-- TheoremDoc Function.HasLeftInverse.injective as "HasLeftInverse.injective" in "Function"
-- Statement Function.HasLeftInverse.injective
Statement {A B : Type} {f : A → B} (h : HasLeftInverse f) :
    Injective f := by
  /-
  Hint "
    **Du**: Eine Abbildung, die ein Linksinverses besitzt, ist injektiv.  Schonmal gehört, glaube ich …
  "
  -/
  Hint "Explain that a mapping, which is left inverse ..."
  intro a a' ha
  obtain ⟨g, hg⟩ := h
  -- Hint "**Robo**:  Vielleicht irgendwas mit `congr_arg g`?"
  Hint "Try using `congr_arg g`"
  Branch
    trans g (f a)
    · rw [hg]
    · rw [ha]
      rw [hg]
  apply congr_arg g at ha
  unfold LeftInverse at hg
  rw [hg a, hg a'] at ha
  assumption

  /-
  Conclusion "
    **Robo**:  Gut gemacht!  Ich glaube, wir sind hier bald durch …
  "
  -/
  Conclusion "Conclusion Mono L09"
