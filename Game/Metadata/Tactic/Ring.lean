import Mathlib.Tactic.Ring

namespace Game

macro (name := ring) "ring" : tactic =>
  `(tactic| first | ring1 | ring_nf)
macro "ring!" : tactic =>
  `(tactic| first | ring1! | ring_nf!)
