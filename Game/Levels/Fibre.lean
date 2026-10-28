import Game.Levels.Fibre.L01_NcardEqTwo
import Game.Levels.Fibre.L02_SecondElement
import Game.Levels.Fibre.L03_ThreePreimages
import Game.Levels.Fibre.L04_ValueAtPair
import Game.Levels.Fibre.L05_MaxInIoo
import Game.Levels.Fibre.L06_ExistsNonpos
import Game.Levels.Fibre.L07_ExistsNonneg
import Game.Levels.Fibre.L08_Boss

/-!
The planet `Fibre` proves that **no continuous function `ℝ → ℝ` takes every value exactly
twice**.  It first develops the counting API for two-element fibres (`ncard_eq_two_lt`,
`exists_second_mem`, `three_preimages`), then combines it with the interval analysis from the
`Bolzano` planet to produce points where `f` is `≤ 0` and `≥ 0` strictly between the two zeros
of `f`.  The boss level `not_exists_continuous_ncard_preimage_eq_two` derives the
contradiction from a third preimage of `0`.
-/

World "Fibre"
Title "Fibre"

Introduction " Intro Fibre"
