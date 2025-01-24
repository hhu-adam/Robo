import Game.Metadata

World "Ciao"
Level 1

Title "Weiter gehts …"

Introduction ""

Statement : ∀ (n : ℕ), ∃ (m : ℕ), m > n := by
  intro n
  use n+1
  linarith

Conclusion "**Du**: Das war ja nun nicht so schwer …

**Robo**:  Ich glaube, das war Leansch für „Es geht immer weiter …”.

**Robo**:  Oh, schau mal, noch eine Nachricht:


*Liebe Erdwesen, es war uns ein Vergnügen, euch kennenzulernen!
Es tut uns aufrichtig leid, dass ihr euch in unser Formaloversum verirrt habt und
nicht wieder nach Hause findet.  Aber wir haben noch eine gute Nachricht:
Ihr seid nicht die einzigen!
Fliegt nur rasch weiter zum Planeten Zulip.
Dort werdet ihr viele weitere Erdwesen finden, die sich ins Formaloversum verirrt haben.
Zulip ist groß, gewiss werdet auch ihr dort einen neues Zuhause finden.  Hier die Koordinaten:*

[248-4804-180 | 844-1001-553](https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/)

Mit den aufrichtigsten Grüßen
– Eure Formalosophen
"
