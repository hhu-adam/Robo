import Game.Metadata


World "Quantus"
Level 7

Title ""

Introduction
"
Inzwischen haben sich in der Menge anscheinend zwei Lager gebildet.
Ihr hört abwechselnd die Rufe „Even“ und „Odd“. Deshalb zeigt dir Robo
vorsichtshalber schon einmal die entsprechende Definition:

```
def Even (n : ℕ) : Prop := ∃ r, n = r + r
```

Bevor er zu `Odd` weitergehen kann,
taucht von irgendwo aus der Menge folgendes Papier auf:
"

Statement : Even 42 := by
  Hint "
    **Robo**: Moment! Dafür brauchst du die Definition gar nicht!

    **Du**: Das ist ja irgendwie trivial…

    **Robo**: Erinnerst du dich? `decide` kann alle Aufgaben lösen, bei denen es einen
    einfachen Algorithmus gibt um die Wahrheit zu bestimmen.
    Aussagen zu konkreten Zahlen fallen meistens in diese Kategorie!
  "
  decide

Conclusion
"
**Du**: Was kann denn `decide` noch alles?

**Robo**: Konkret hat hier jemand einen ausführbaren
Algorithmus angegeben, wie entschieden werden
soll, ob `Even 42` wahr oder falsch ist. Wenn `decide` also so einen Algorithmus kennt,
dann kann es die Aufgabe lösen.
"

OnlyTactic decide
