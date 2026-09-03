import Game.Levels.Bolzano.L01_MaxOnIcc
import Game.Levels.Bolzano.L02_CrossLeft
import Game.Levels.Bolzano.L03_CrossRight
import Game.Levels.Bolzano.L04_ZeroBetween

/-!
The planet `Bolzano` is about *continuous functions on an interval*.  It starts from the fact
that a continuous function attains a maximum on a closed interval `Icc a b`
(`IsCompact.exists_isMaxOn`), and then re-uses the intermediate value theorem in the form met
on the `Shade` planet (`intermediate_value_Ioo` and `intermediate_value_Ioo'`) to build the
tools the `Fibre` planet needs: the two "crossing" lemmas, saying that a function running from
`0` up to `f m` across an interval attains every value in between strictly inside it, and the
boss level, saying that a sign change inside an open interval produces a zero there.
-/

World "Bolzano"
Title "Bolzano"

Introduction " Intro Bolzano"
