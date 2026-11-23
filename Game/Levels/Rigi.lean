import Game.Levels.Rigi.L01_ShadeDef
import Game.Levels.Rigi.L02_ShadeDefSymm
import Game.Levels.Rigi.L03_MemSun
import Game.Levels.Rigi.L04_ShadeSetNonempty
import Game.Levels.Rigi.L05_ShadeSetBddAbove
import Game.Levels.Rigi.L06_LtSSupShaders
import Game.Levels.Rigi.L07_ValLeValSSupShaders
import Game.Levels.Rigi.L08_ValRightOfSSup
import Game.Levels.Rigi.L09_InterValue
import Game.Levels.Rigi.L10_InterValueSymm
import Game.Levels.Rigi.L11_Boss

/-!
The planet `Rigi` is about the *Rising Sun Lemma* (Light and Shadow). It builds on
the bounds/suprema API developed on `Aquarius`, introduces the `Shade`/`Sun` definitions
and their API, applies the intermediate value theorem, and culminates in the boss theorem
`f a = f b`.
-/

World "Rigi"
Title "Rigi"


Introduction "Intro Rigi"
