import Game.Metadata
import Game.Levels.Implis -- to make sure `rw` doc is imported

World "Spinoza"
Level 4

Title ""

/-
Introduction
"
**Benedictus**: Ich habe noch eine schöne Frage zu ungeraden Quadraten für Euch.
Aber vorher beweist Ihr besser noch diese Äquivalenz hier. Ich glaube, die hat sogar
bei Euch einen Namen: *Kontrapositionsäquivalenz*, oder so etwas. Auf Leansch nennen wir
die Äquivalenz einfach `not_imp_not`. Ist doch viel einleuchtender, oder?
"
-/
Introduction "Intro Spinoza L04: introduce contraposition equivalence with `not_imp_not`"

/---/
TheoremDoc not_imp_not as "not_imp_not" in "Logic"

Statement not_imp_not (A B : Prop) : A → B ↔ (¬ B → ¬ A) := by
  /-
  Hint "
    **Du**: Ja, das habe ich tatsächlich schon einmal gesehen.

    **Robo**: Ja, klar hast du das schon einmal gesehen. Das benutzen Mathematiker doch ständig.
    Wenn ihnen zu $A ⇒ B$ nichts einfällt, zeigen sie stattdessen $¬B ⇒ ¬A$. Ich würde das ja
    statt *Kontraposition* eher *von_hinten_durch_die_Brust_ins_Auge* nennen.
    Aber hier heißt es natürlich `not_imp_not`."
  -/
  Hint "Often to prove $A ⇒ B$, $¬B ⇒ ¬A$ can be proven as well. Here this is called `not_imp_not`."
  -- Hint (hidden := true) "**Robo**: Fang doch mal mit `constructor` an."
  Hint (hidden := true) "Start trying with `constructor`"
  constructor
  intro h b
  by_contra a
  -- Hint "**Robo**: Ich würde wieder mit `suffices g : B` einen Widerspruch herbeiführen."
  Hint "Provoce contradiction by using `suffices g : B`"
  suffices b : B
  contradiction
  apply h
  assumption
  intro h a
  -- Hint "**Robo**: Hier würde ich ebenfalls einen Widerspruchsbeweis anfangen."
  Hint "`COMMENT` Use proof by contradiction"
  by_contra b
  -- Hint (hidden := true) "**Robo**: `suffices g : ¬ A` sieht nach einer guten Option aus."
  Hint (hidden := true) "`suffices g : ¬ A` would be a good option"
  suffices g : ¬ A
  contradiction
  apply h
  assumption

-- Conclusion ""
Conclusion "Conclusion Spinoza L04"

DisabledTactic rw tauto
DisabledTheorem Classical.not_not
TheoremTab "Logic"
