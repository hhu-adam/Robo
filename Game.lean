import Game.Metadata

import Game.Levels.Logos
import Game.Levels.Implis
import Game.Levels.Quantus

import Game.Levels.Spinoza
import Game.Levels.Luna
import Game.Levels.Babylon

import Game.Levels.Cantor
import Game.Levels.Robotswana

import Game.Levels.End

import Game.Levels.NewStuff.Prime

import Game.Levels.FunctionSurj
import Game.Levels.FunctionInj
import Game.Levels.FunctionBij
-- import Game.Levels.SetTheory

-- *uncomment the following line to get the incomplete planets.*
-- import Game.DevPlanets

Title "Robo"
Introduction
"
# Game Over oder QED?

Willkommen zu unserem Prototyp eines Lean4-Lernspiels. Hier lernst du computer-gestützte
Beweisführung. Das Interface ist etwas vereinfacht, aber wenn du den *Editor Mode* aktivierst, fühlt es sich
fast genauso an wie in VSCode, der Standard-IDE für Lean.

Rechts siehst du eine Übersicht. Das Spiel besteht aus mehreren Planeten, und jeder Planet hat mehrere Levels,
die in Form von grauen Punkten dargestellt sind. Gelöste Levels werden grün.

Klicke auf den ersten Planeten *Logo*, um deine Reise zu starten.


### More
Schau im Menü unter \"Game Info\" für mehr Informationen zum Spiel.
"

Info
"
## Spielstand

Dein Spielstand wird lokal in deinem Browser als *site data* gespeichert.
Solltest du diese löschen, verlierst du deinen Spielstand!
Viele Browser löschen *site data* und *cookies* zusammen.
Wenn du \"Game rules: lax\" auswählst kannst aber jederzeit jedes Level spielen,
auch wenn du vorhergende Levels noch nicht gelöst hast.

## Funding

Dieses Lernspiel wurde und wird im Rahmen des Projekts
[ADAM: Anticipating the Digital Age of Mathematics](https://hhu-adam.github.io/)
an der Heinrich-Heine-Universität Düsseldorf entwickelt.
Es wird finanziert durch das Programm *Freiraum 2022* der
*Stiftung Innovation in der Hochschullehre*.

## Credits

* **Creators:** Jon Eugster, Alexander Bentkamp, Marcus Zibrowius, Sina Hazratpour
* **Game Engine:** Alexander Bentkamp, Jon Eugster, Patrick Massot
* **Illustrationen:** Dušan Pavlić

## Kontakt

Das Spiel befindet sich noch in der Entwicklung.
Wenn du Anregungen hast oder Bugs findest, schreib doch ein Email oder erstelle einen
Issue auf Github:

* zum Spielinhalt im [Robo repo](https://github.com/hhu-adam/Robo/issues).
* zum Spielserver im [lean4game repo](https://github.com/leanprover-community/lean4game/issues).

Kontakt: [Jon Eugster](https://www.math.hhu.de/lehrstuehle-/-personen-/-ansprechpartner/innen/lehrstuehle-des-mathematischen-instituts/lehrstuhl-fuer-algebraische-geometrie/team/jon-eugster)
"

Conclusion
"Fertig!"


/-! Information to be displayed on the servers landing page. -/
Languages "de"
CaptionShort "Erkunde das Leansche Universum mit deinem Robo, welcher dir bei der Verständigung mit den Formalosophen zur Seite steht."
CaptionLong "Dieses Spiel führt die Grundlagen zur Beweisführung in Lean ein und schneidet danach verschiedene Bereiche des Bachelorstudiums an.

(Das Spiel befindet sich noch in der Entstehungsphase.)"
-- Prerequisites "" -- add this if your game depends on other games
CoverImage "images/Cover.png"


/-! If you need to add manual dependencies in your planet graph, you can do so here: -/

Dependency Robotswana → End
Dependency Cantor → End

-- Dependency Babylon → FunctionSurj


-- because of `∃!`
Dependency Prime → FunctionInj
-- Because of def `Injective`
Dependency FunctionInj → FunctionBij


set_option lean4game.showDependencyReasons true

/-! Build the game. Show's warnings if it found a problem with your game.

(need to open all namespaces with local definitions) -/
open BigOperators in
MakeGame
