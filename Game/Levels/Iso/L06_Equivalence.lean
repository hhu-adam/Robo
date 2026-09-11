import Game.Metadata

World "Iso"
Level 6

/-
Introduction
"
An equivalence `α : A ≃ B` between `A` and `B` consists of a pair of functions `f : A → B` and `g : B → A` such that `f ∘ g = id` and `g ∘ f = id`.

`finTwoArrowEquiv` constructs an equivalence between functions from `Fin 2` to `A` and pairs of elements of `A`, that is an equivalence
  ```
  (Fin 2 → A) ≃ A × A

  ```
In this level you construct an equivalence between functions from `Fin 3` to `A` and triples of elements of `A`.
"
-/
Introduction "Intro Iso L06"

open Function

Statement {A : Type} : (Fin 3 → A) ≃ A × A × A := by
  Hint "[Hint q7vk2] Build the equivalence by hand, as you did for currying.
    Start by constructing a candidate for the forward map `f : (Fin 3 → A ) → A × A × A`.
    Recall that a triple in `A × A × A` is written as `(a, (b, c))`, or simply `(a, b, c)`."
  let f := fun (f : Fin 3 → A) ↦ ((f 0, (f 1, f 2)) : A × A × A)
  Hint "[Hint elxld] Now the inverse map:  Remember that the function `Fin 3 → A` sending
    `0 ↦ a`, `1 ↦ b` and `2 ↦ c` is denoted `![a, b, c] : Fin 3 → A`."
  Hint (hidden := true) "[Hint 9s56i] Also remember that `A × A × A` is really `A × (A × A)`, so
    the components of `t : A × A × A` are called `t.1`, `t.2.1` and `t.2.2`."
  let g := fun (t : A × A × A ) ↦ ![ t.1, t.2.1, t.2.2]
  Hint (hidden := true) "[Hint g0kn2] `refine ⟨{f}, {g}, ?_, ?_⟩` sets `toFun` to `{f}` and
    `invFun` to `{g}`, leaving the proofs of `left_inv` and `right_inv` as goals."
  refine ⟨f, g, ?_, ?_⟩
  · Hint (hidden := true) "[Hint v8rq2] Unfold `LeftInverse`, `{f}` and `{g}` and simplify."
    simp [LeftInverse, f, g]
    intro f'
    Hint (hidden := true) "[Hint k3mwt] Two functions are equal as soon as they agree on every
      argument — that is `funext`."
    funext x
    Hint (hidden := true) "[Hint dz6pf] Only three values of `x` are possible;
      `fin_cases x` treats them one by one."
    fin_cases x
    · Hint (hidden := true) "[Hint n5hjb] Try `simp`."
      simp
    · simp
    · simp
  · Hint (hidden := true) "[Hint t7gks] Unfold `RightInverse`, `LeftInverse`, `{f}` and `{g}`,
      then simplify."
    simp [RightInverse, LeftInverse, f, g]


/- Already in the place introduce vector.-/
NewTactic fin_cases
-- TODO: fin_cases should be in set-theory
