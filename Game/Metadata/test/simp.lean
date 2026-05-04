import Game.Metadata.Tactic.Simp

-- behaviour without custom simp (comment import line above)
/-
example : 1 + 1 = 2 := by simp                   -- works, as expected
example : 1 + 1 = 2 := by simp?                  -- suggests simp only [Nat.reducedAdd], as expected
example (I : Finset ℕ) : (∑ i ∈ I, 1) = Finset.card I := by simp -- work, as expected
example (I : Finset ℕ) : (∑ i ∈ I, 1) = Finset.card I := by simp only [game_simp] fails, as expected
-/

@[game_simp] theorem my_test_lemma : 1 + 1 = 2 := by norm_num
--#check @game_simp

example : 1 + 1 = 2 := by simp                   -- works (as expected)
example : 1 + 1 = 2 := by simp?                  -- suggests simp only [my_test_lemma], as intended
--example (I : Finset ℕ) : (∑ i ∈ I, 1) = Finset.card I := by simp  -- fails, as intended
--example (I : Finset ℕ) : (∑ i ∈ I, 1) = Finset.card I := by simp? -- fails, as intended
attribute [game_simp] Finset.sum_const smul_eq_mul mul_one
example (I : Finset ℕ) : (∑ i ∈ I, 1) = Finset.card I := by simp  -- now works, as intended
example (I : Finset ℕ) : (∑ i ∈ I, 1) = Finset.card I := by simp? -- now works, as intended


/-macro "true_simp" : tactic
  => `(tactic| simp (config := {}))
macro "true_simp" "[" args:Lean.Parser.Tactic.simpLemma,* "]" : tactic
  => `(tactic| simp (config := {}) [$args,*])
macro "true_simp" "at" loc:Lean.Parser.Tactic.locationHyp : tactic
  => `(tactic| simp (config := {}) at $loc)
macro "true_simp" "[" args:Lean.Parser.Tactic.simpLemma,* "]" "at" loc:Lean.Parser.Tactic.locationHyp : tactic
  => `(tactic| simp (config := {}) [$args,*] at $loc)
-/

--example : 1 + 1 = 2 := by true_simp                   -- works (as expected)
example : 1 + 1 = 2 := by true_simp?                  -- suggests [Nat.reducedAdd]
--example (I : Finset ℕ) : (∑ i ∈ I, 1) = Finset.card I := by true_simp  -- works, as intended
example (I : Finset ℕ) : (∑ i ∈ I, 1) = Finset.card I := by true_simp? -- works, as intended

#print Lean.Meta.SimpTheorems
