1. L01. can already use `grind` on line 80 – too strong!
2. L03. after unfold `IsFixedPt` then `grind`.
3. L06. change the proof to be first `unfold IsFixedPt` then `grind`
4. L07. after `apply congr_fun at h (line 44)` then `grind`. but not `grind (ematch := 0)`.
5. L08. after `unfold IsFixedPt`, then `grind`. also `grind (ematch := 0)`.
6. L09. after `unfold` then `grind`.
