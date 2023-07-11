import Game.Metadata

import Game.Levels.Proposition
import Game.Levels.Implication
import Game.Levels.Predicate
import Game.Levels.Contradiction
-- import Game.Levels.Prime
import Game.Levels.Sum
-- import Game.Levels.Induction

--import Game.Levels.Numbers
import Game.Levels.Inequality

import Game.Levels.Lean
import Game.Levels.SetTheory
import Game.Levels.Function
--import Game.Levels.SetFunction
--import Game.Levels.LinearAlgebra



Title "Lean 4 game"
Introduction
"
# Game Over oder QED?

Willkommen zu unserem Prototyp eines Lean4-Lernspiels. Hier lernst du computer-gestützte
Beweisführung. Das Interface ist etwas vereinfacht, aber wenn du den *Editor Mode* aktivierst, fühlt es sich
fast genauso an wie in VSCode, der Standard-IDE für Lean.

Rechts siehst du eine Übersicht. Das Spiel besteht aus mehreren Planeten, und jeder Planet hat mehrere Levels,
die in Form von grauen Punkten dargestellt sind. Gelöste Levels werden grün.

Klicke auf den ersten Planeten *Logo*, um deine Reise zu starten.

### Spielstand

Dein Spielstand wird lokal in deinem Browser als *site data* gespeichert.
Solltest du diese löschen, verlierst du deinen Spielstand!
Viele Browser löschen *site data* und *cookies* zusammen.
Du kannst aber jederzeit jedes Level spielen, auch wenn du vorhergende Levels noch nicht gelöst hast.

### Funding

Dieses Lernspiel wurde und wird im Rahmen des Projekts
[ADAM: Anticipating the Digital Age of Mathematics](https://hhu-adam.github.io/)
an der Heinrich-Heine-Universität Düsseldorf entwickelt.
Es wird finanziert durch das Programm *Freiraum 2022* der *Stiftung Innovation in der Hochschullehre*.

### Kontakt

Das Spiel befindet sich noch in der Entwicklung.
Wenn du Anregungen hast oder Bugs findest, schreib doch ein Email oder erstelle einen
[Issue auf Github](https://github.com/leanprover-community/lean4game/issues).

[Jon Eugster](https://www.math.hhu.de/lehrstuehle-/-personen-/-ansprechpartner/innen/lehrstuehle-des-mathematischen-instituts/lehrstuhl-fuer-algebraische-geometrie/team/jon-eugster)
"

Conclusion
"Fertig!"

MakeGame
