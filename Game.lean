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
import Game.Levels.Euklid

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

Das Interface ist etwas vereinfacht, aber wenn du den *Editor-Modus* aktivierst, fühlt es sich
fast genauso an wie in VSCode, der Standard-IDE für Lean.
Auf einem Smartphone oder Tablet bleibst du besser im voreinsgestellten *Schreibmaschinen-Modus*, und schaltest alle autocompletion/correction Features deiner Bildschirmtastatur aus (z.B. unter „intelligentes Tippen > Texterkennung“ auf Samsung-Tastur).

Klicke auf den ersten Planeten *Logo* in der Übersicht, um deine Reise zu starten.

## Spielstand

Dein Spielstand wird lokal in deinem Browser als *site data* gespeichert.
Solltest du diese löschen, verlierst du deinen Spielstand!
Viele Browser löschen *site data* und *cookies* zusammen.
Du kannst den Spielstand aber auch über das Menü herunterladen und manuell speichern.

## Spielregeln

Wenn du ernsthaft spielen möchtest, solltest du *Rules: regular* wählen.
Wenn du dich nur ein bisschen umsehen möchtest, wähle *Rules: relaxed*
  – dann kannst du jedes Level spielen, auch wenn du vorhergende Levels noch nicht gelöst hast.

## Neuigkeiten
`[2025-03-24]` Der jüngste Planet im Formaloversum heißt Euklid.
Ansonsten gab es jede Menge kleiner Verbesserungen.
Insbesondere wird auf Babylon jetzt über Intervalle in ℕ und ℤ summiert, und nicht mehr über `Fin n`.

Die nächsten und vorläufig letzten Planeten, die noch einmal überarbeitet werden werden, sind Cantor und Robotswana.

`[2025-03-18]` Von Quantus hat sich der Planet Saturn abgespalten, Luna ist größer geworden, und auch Piazza wurde grundlegend überarbeitet.

Leider war nach dem Update wegen Problemen mit unserer Speicherverwaltung das Spiel für mehrere Stunden nicht verfügbar.
Wir arbeiten daran, dass das in Zukunft reibungsloser verläuft.

`[2025-02-20]` Die „Abbildungsplaneten“ sind fertig:  Vieta, Mono, Epo, Iso und Samarkand.
Viel Spaß auf ihnen!

`[2025-01-25]` Es gibt jetzt einen Planeten, um sich zu verabschieden:  Ciao.

Hintergrundinformationen und Credits findest du im Menü unter *Game Info*.
"

Info
"
## Projekt ADAM

Dieses Lernspiel wurde im Rahmen des Projekts
[ADAM: Anticipating the Digital Age of Mathematics](https://hhu-adam.github.io/)
an der Heinrich-Heine-Universität Düsseldorf entwickelt,
finanziert durch das Programm *Freiraum 2022* der *Stiftung Innovation in der Hochschullehre*.

## Spielinhalt

**Spoiler Alert** Auf [Github](https://github.com/hhu-adam/Robo?tab=readme-ov-file#overview-over-existing-content) findest du eine Übersicht über den groben mathematischen Inhalt aller Planeten.

## Credits

* **Projektleitung:** Marcus Zibrowius, Immi Halupczok
* **Game Engine:** Jon Eugster, Alexander Bentkamp, Patrick Massot – siehe [lean4game](https://github.com/leanprover-community/lean4game?tab=readme-ov-file#credits)
* **Levels:** Jon Eugster, Marcus Zibrowius, Sina Hazratpour
* **Konzept & Handlung:** Marcus Zibrowius
* **Illustrationen:** [Dušan Pavlić](https://www.behance.net/dusanpavlic#)

## Kontakt

Das Spiel wird laufend überarbeitet.
Wir freuen uns sehr über Erfahrungsberichte, Anregungen und Kritik,
zum Beispiel per Email an
[Marcus Zibrowius](https://www.math.uni-duesseldorf.de/~zibrowius/).
Wenn du spezifische Änderungswünsche hast oder Fehler findest, kannst du auch gern einen Issue auf GitHub erstellen:

* zum Spielinhalt im [Robo repo](https://github.com/hhu-adam/Robo/issues)
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
Dependency Euklid → Ciao

-- set_option lean4game.showDependencyReasons true

/-! Build the game. Show's warnings if it found a problem with your game.

(need to open all namespaces with local definitions) -/
-- open BigOperators in
MakeGame
