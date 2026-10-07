import Game.Metadata

World "Cartan"
Level 5

open Topology Filter

Statement {a : ℝ} (hab : a < 0) :
    ∀ᶠ x in 𝓝 a, x < 0 := by
  Hint "[Hint zntfk] For a filter `𝓕`, `∀ᶠ x in 𝓕, p x` says that `p x` holds *eventually*,
  i.e. the set `\{ x | p x}` is a member of 𝓕."
  apply eventually_lt_nhds
  assumption

/---/
TheoremDoc eventually_lt_nhds as "eventually_lt_nhds"
/---/
TheoremDoc eventually_gt_nhds as "eventually_gt_nhds"


NewTheorem eventually_lt_nhds eventually_gt_nhds
