1. L03: directly solved by `grind`. (solution: `grind (ematch := 0)`)
2. L06: after `obtain ⟨hp₁, hp⟩ := hp`, then `grind`, but `grind (ematch := 0)` failed. This is used to introduce `specialize`.
3. L10: after `rw [prime_def] at hp`, then `grind`.
