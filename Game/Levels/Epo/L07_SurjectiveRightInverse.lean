import Game.Metadata


World "Epo"
Level 7

Title ""

Introduction ""

open Set

/---/
TheoremDoc Function.surjective_iff_hasRightInverse as "surjective_iff_hasRightInverse" in "Function"

namespace Function

Statement surjective_iff_hasRightInverse {A B : Type} (f : A → B) :
    Surjective f ↔ HasRightInverse f := by
  constructor
  · intro hs
    choose g hg using hs
    -- unfold HasRightInverse
    use g
    assumption
  · -- this is `Function.HasRightInverse.surjective`
    intro ⟨g, inv⟩
    intro b
    use g b
    apply inv

TheoremTab "Function"

/-
Conclusion "
Ihr bekommt eine große Runde Applaus.

Danach werdet ihr verabschiedet.
Für den Rückweg könnt ihr leider keine Transportkapsel benutzen.
Die funktionieren nämlich nur in eine Richtung.
Zurück zum Raumschiff geht es also zu Fuß: erst die Treppen runter, dann draußen vom Bürohaus zum Schlafturm, und schließlich mit einem ganz gewöhnlichen Fahrstuhl nach oben.
"
-/
Conclusion "`CONC` Conclusion Epo L07"
