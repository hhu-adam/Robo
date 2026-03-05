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
/-
# Game Over or QED

Are you curious about how computer-assisted reasoning feels compared to “real” mathematics?
Then you've come to the right place!In this game, you will learn how to work with the proof assistant Lean 4 and the proof library mathlib.
Among other things, you will prove sum formulas by induction, prove that a mapping is surjective if and only if it has a right inverse,
show that there are uncountably many sequences of natural numbers, and characterize the trace as a mapping on the space of square matrices.
The interface is somewhat simplified, but if you activate *editor mode*, it feelsalmost exactly like VSCode,
the standard IDE for Lean.
On a smartphone or tablet, it's better to stay in the default *typewriter mode* and turn off all
autocompletion/correction features on your on-screen keyboard (e.g., under “smart typing > text recognition” on Samsung keyboards).
Click on the first planet *logo* in the overview to start your journey.

## Game score

Your game score is stored locally in your browser as *site data*.
If you delete this, you will lose your game score!
Many browsers delete *site data* and *cookies* together.
However, you can also download your game score from the menu and save it manually.

## Rules of the game

If you want to play seriously, you should choose *Rules: regular*.
If you just want to have a look around, choose *Rules: relaxed*
  – then you can play any level, even if you haven't solved the previous levels yet.

## News
`[2025-03-28]` The youngest planet in the Formaloversum is called Euclid.
There are also lots of minor improvements, especially on Babylon, Cantor, and Saturn,
and in the documentation of tactics and definitions.
On Babylon, intervals are now summed over ℕ and ℤ, and no longer over `Fin n`.
Saturn now ends with a polynomial square sum formula.

`[2025-03-18]` The planet Saturn has split off from Quantus, Luna has grown larger, and Piazza has also been fundamentally revised.

`[2025-02-20]` The “image planets” are complete:  Vieta, Mono, Epo, Iso, and Samarkand.

`[2025-01-25]` There is now a planet to say goodbye:  Ciao.

Background information and credits can be found in the menu under *Game Info*."
-/
"[Main game intro]"

Info
/-
## Project ADAM

This educational game was developed as part of the project
[ADAM: Anticipating the Digital Age of Mathematics](https://hhu-adam.github.io/)
at Heinrich Heine University Düsseldorf,
funded by the *Freiraum 2022* program of the *Stiftung Innovation in der Hochschullehre* (Foundation for Innovation in Higher Education).
Ongoing maintenance and development are generously supported by *Renaissance Philanthropy* through the *AI for Math Fund*.

## Game content

**Spoiler alert** You can find an overview of the rough mathematical content of all planets on [Github](https://github.com/hhu-adam/Robo?tab=readme-ov-file#overview-over-existing-content).

## Credits

* **Project management:** Marcus Zibrowius, Immi Halupczok
* **Game engine:** Jon Eugster, Alexander Bentkamp, Patrick Massot – see [lean4game](https://github.com/leanprover-community/lean4game?tab=readme-ov-file#credits)
* **Levels:** Jon Eugster, Marcus Zibrowius, Sina Hazratpour
* **Concept & Story:** Marcus Zibrowius
* **Illustrations:** [Dušan Pavlić](https://www.behance.net/dusanpavlic#)

## Contact

The game is constantly being revised.
We welcome your feedback, suggestions, and criticism,
for example, by email to
[Marcus Zibrowius](https://www.math.uni-duesseldorf.de/~zibrowius/).
If you have specific change requests or find errors, you are also welcome to create an issue on GitHub:

* for game content in the [Robo repo](https://github.com/hhu-adam/Robo/issues)
* for the game server in the [lean4game repo](https://github.com/leanprover-community/lean4game/issues).
-/
"[Game info]"

Conclusion
/-
QED
-/
"[Game conclusion]"


/-! Information to be displayed on the servers landing page. -/
Languages "de"
CaptionShort -- "Erkunde ein fremdes Universum mit deinem Smart-Elf Robo!"
"Explore an alien universe with the Smart-Elf Robo!"
CaptionLong "This game illustrates reasoning with Lean using various topics from the introductory phase of the bachelor's degree program in mathematics."
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
