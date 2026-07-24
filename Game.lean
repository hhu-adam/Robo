import Game.Metadata

import Game.Levels.Logo
import Game.Levels.Implis
import Game.Levels.Quantus

import Game.Levels.Saturn
import Game.Levels.Spinoza
-- Luna is disabled: its remaining levels stay in the repo but are no longer part of the game.
-- import Game.Levels.Luna
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

import Game.Levels.Cafe

import Game.Levels.Cartan
import Game.Levels.Aquarium
import Game.Levels.Shade
import Game.Levels.Slope

-- *uncomment the following line to get the incomplete planets.*
-- import Game.DevPlanets

Title "[Game] Title"
Introduction "[Game] Introduction"
Info "[Game] Info"

Conclusion "[Game] Conclusion"


/-! Information to be displayed on the servers landing page. -/
Languages "de" "en" "zh"
CaptionShort "[Game] CaptionShort"
CaptionLong  "[Game] CaptionLong"
Prerequisites "[Game] Prerequisites"
CoverImage "images/Cover.png"


/-! If you need to add manual dependencies in your planet graph, you can do so here: -/
Dependency Quantus → Piazza -- because of `∀`
-- Dependency Quantus → Cafe -- because of `ring`
Dependency Prado → Mono     -- because of `∃!`
Dependency Mono → Iso       -- because of `Injective`
Dependency Vieta → Shade    -- because of `function`

Dependency Vieta → Aquarium -- because of `function`
Dependency Vieta → Cartan   -- because of `function`

Dependency Robotswana → Ciao
Dependency Cantor → Ciao
Dependency Samarkand → Ciao
Dependency Iso → Ciao
Dependency Euklid → Ciao

-- set_option lean4game.showDependencyReasons true

/-! Build the game. Show's warnings if it found a problem with your game.

Need to open namespaces with local definitions and notation for the inventory to display correctly.
-/
-- open BigOperators
open Topology in
MakeGame
