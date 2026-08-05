import Game.Levels.Aquarium.L01_UpperBounds
import Game.Levels.Aquarium.L02_BddAbove
import Game.Levels.Aquarium.L03_Le_csSup
import Game.Levels.Aquarium.L04_CsSup_le
import Game.Levels.Aquarium.L05_IsClosed_le
import Game.Levels.Aquarium.L06_Closure_minimal
import Game.Levels.Aquarium.L07_CsSup_mem_closure

/-!
The planet `Aquarium` is about *bounds and suprema*: `upperBounds`, `BddAbove`, `csSup`/`sSup`,
closures and `csSup_mem_closure`, building the analysis API that the `Shade`
planet (Rising Sun Lemma) relies on. The boss level `csSup_mem_closure` ties the
bound/supremum results together.
-/

World "Aquarium"
Title "Aquarium"

Introduction " Intro Aquarium"
