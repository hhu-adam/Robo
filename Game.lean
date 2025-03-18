import Game.Metadata

import Game.Levels.Logo
import Game.Levels.Implis
import Game.Levels.Quantus

import Game.Levels.Saturn
import Game.Levels.Spinoza
import Game.Levels.Luna
import Game.Levels.Babylon

import Game.Levels.Cantor
import Game.Levels.Robotswana

import Game.Levels.Ciao

import Game.Levels.Prado

import Game.Levels.Vieta
import Game.Levels.Epo
import Game.Levels.Mono
import Game.Levels.Samarkand
import Game.Levels.Iso

import Game.Levels.Piazza

-- *uncomment the following line to get the incomplete planets.*
-- import Game.DevPlanets

Title "Robo"
Introduction
"
# Game Over oder QED?

Bist du neugierig, wie sich computer-unterstützte Beweisführung mit „echter“ Mathematik anfühlt?
Dann bist du hier genau richtig!
In diesem Spiel lernst du, mit dem Beweisassistenten Lean 4 und der Beweisbibliothek Mathlib zu arbeiten.

Das Interface ist etwas vereinfacht, aber wenn du den *Editor Mode* aktivierst, fühlt es sich
fast genauso an wie in VSCode, der Standard-IDE für Lean.

Rechts siehst du eine Übersicht. Das Spiel besteht aus mehreren Planeten, und jeder Planet hat mehrere Levels,
die in Form von grauen Punkten dargestellt sind. Gelöste Levels werden grün.

Klicke auf den ersten Planeten *Logo*, um deine Reise zu starten.

## Spielstand

Dein Spielstand wird lokal in deinem Browser als *site data* gespeichert.
Solltest du diese löschen, verlierst du deinen Spielstand!
Viele Browser löschen *site data* und *cookies* zusammen.
Du kannst den Spielstand aber auch über das Menü herunterladen und manuell speichern.

## Spielregeln

Wenn du ernsthaft spielen möchtest, solltest du *Rules: regular* wählen.
Wenn du dich nur ein bisschen umsehen möchtest, wähle *Rules: relaxed*
  – dann kannst du jedes Level spielen, auch wenn du vorhergende Levels noch nicht gelöst hast.

Hintergrundinfos findest du im Menü unter *Game Info*.
"

Info
"
## Projekt ADAM

Dieses Lernspiel wurde im Rahmen des Projekts
[ADAM: Anticipating the Digital Age of Mathematics](https://hhu-adam.github.io/)
an der Heinrich-Heine-Universität Düsseldorf entwickelt,
finanziert durch das Programm *Freiraum 2022* der *Stiftung Innovation in der Hochschullehre*.

## Credits

* **Projektleitung:** Marcus Zibrowius, Immi Halupczok
* **Game Engine:** Jon Eugster, Alexander Bentkamp, Patrick Massot – siehe [lean4game](https://github.com/leanprover-community/lean4game?tab=readme-ov-file#credits)
* **Levels:** Jon Eugster, Marcus Zibrowius, Sina Hazratpour
* **Konzept & Handlung:** Marcus Zibrowius
* **Illustrationen:** [Dušan Pavlić](https://www.behance.net/dusanpavlic#)

## Kontakt

Das Spiel wird laufend überarbeitet.
Wenn du Anregungen hast oder Bugs findest, schreib doch ein Email an
[Marcus Zibrowius](https://www.math.uni-duesseldorf.de/~zibrowius/)
oder erstelle einen Issue auf GitHub:

* zum Spielinhalt im [Robo repo](https://github.com/hhu-adam/Robo/issues).
* zum Spielserver im [lean4game repo](https://github.com/leanprover-community/lean4game/issues).
"

Conclusion
"QED"


/-! Information to be displayed on the servers landing page. -/
Languages "de"
CaptionShort "Erkunde ein fremdes Universum mit deinem Smart-Elf Robo!"
CaptionLong "Dieses Spiel illustriert Beweisführung mit Lean anhand verschiedener Themen aus der Eingangsphase des Bachelorstudiums Mathematik."
-- Prerequisites "" -- add this if your game depends on other games
CoverImage "images/Cover.png"


/-! If you need to add manual dependencies in your planet graph, you can do so here: -/
Dependency Quantus → Piazza -- because of `∀`
Dependency Prado → Mono     -- beclause of `∃!`
Dependency Mono → Iso       -- because of `Injective`

Dependency Robotswana → Ciao
Dependency Cantor → Ciao
Dependency Samarkand → Ciao
Dependency Iso → Ciao

-- set_option lean4game.showDependencyReasons true

/-! Build the game. Show's warnings if it found a problem with your game.

(need to open all namespaces with local definitions) -/
-- open BigOperators in
MakeGame
