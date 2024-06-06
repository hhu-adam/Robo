import Game.Metadata

World "Implication"
Level 9

Title "Genau dann, wenn"

Introduction
"
**Du**: Irgendwie fühlen sich diese `rw` an, als würde man von hinten durch den Bauch argumentieren.  Geht das nicht auch irgendwie geradeaus, oder denken alle hier um die Ecke?

**Robo**:  Vielleicht würde dir `trans' besser gefallen.  Damit könntest du deine Kette von Äquivalenzen  $B \\iff A \\iff D \\iff C$ Schritt für Schritt abarbeiten: als erstes führst Du mit `trans A` den Zwischenschritt `B \\iff A` ein, dann mit `trans D` den nächsten Zwischenschritt.
"

Statement (A B C D : Prop) (h₁ : C ↔ D) (h₂ : A ↔ B) (h₃ : A ↔ D) : B ↔ C := by
  trans A
  symm
  assumption
  trans D
  assumption
  symm
  assumption
Conclusion
"
**Robo**: Und, war das besser? 

**Du**:  Weiß nicht.  Wir können jedenfalls weitermachen.
"

NewTactic trans

DisabledTactic tauto rw nth_rw
