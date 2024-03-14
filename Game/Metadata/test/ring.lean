import Game. Metadata.Tactic.Ring

example {n : ℕ} (h : n = 2) : n + 5 = 7 := by
  ring -- silent
  rw [h]
  ring
