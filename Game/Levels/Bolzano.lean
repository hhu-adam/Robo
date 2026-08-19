import Game.Levels.Bolzano.L01_MaxOnIcc
import Game.Levels.Bolzano.L02_MemUIcc
import Game.Levels.Bolzano.L03_IntermediateValue
import Game.Levels.Bolzano.L04_GetPreimage
import Game.Levels.Bolzano.L05_CrossLeft
import Game.Levels.Bolzano.L06_CrossRight

/-!
The planet `Bolzano` is about *continuous functions on a closed interval*: a continuous
function on `Icc a b` attains a maximum (`IsCompact.exists_isMaxOn`), and the intermediate
value theorem on `uIcc` (`intermediate_value_uIcc`).  From these the planet builds the
two "crossing" lemmas used on the `Fibre` planet: if `f` vanishes at one endpoint and reaches
the value `f m` at the other, then every value strictly between `0` and `f m` is attained
strictly inside the interval — once for the zero sitting on the left (`L05`) and once for the
zero sitting on the right (`L06`).
-/

World "Bolzano"
Title "Bolzano"

Introduction " Intro Bolzano"
