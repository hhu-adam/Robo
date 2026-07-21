import Game.Levels.Shade.L01_ShadeDef
import Game.Levels.Shade.L02_ShadeDefSymm
import Game.Levels.Shade.L03_MemSun
import Game.Levels.Shade.L04_ShadeSetNonempty
import Game.Levels.Shade.L05_ShadeSetBddAbove
import Game.Levels.Shade.L06_LtSSupShaders
import Game.Levels.Shade.L07_ValLeValSSupShaders
import Game.Levels.Shade.L08_InterValue
import Game.Levels.Shade.L09_InterValueSymm
import Game.Levels.Shade.L10_Boss

/-!
The planet `Shade` is about the *Rising Sun Lemma* (Light and Shadow). It builds on
the bounds/suprema API developed on `Culmen`, introduces the `Shade`/`Sun` definitions
and their API, applies the intermediate value theorem, and culminates in the boss theorem
`f a = f b`.
-/

World "Shade"
Title "Shade"

Introduction " Intro Shade"
