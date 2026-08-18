import Game.Metadata

World "Iso"
Level 3

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
Introduction "Intro Iso L03"

open Function

Statement {A : Type} : (Fin 3 → A) ≃ A × A × A := by
  Hint "[Hint q7vk2] An equivalence `A ≃ B` is not a proposition but *data*: a map
  `toFun : A → B`, a backwards map `invFun : B → A`, and two proofs `left_inv`, `right_inv`
  saying that these undo each other.
  Remember that `![a, b, c] : Fin 3 → A` denotes the function sending `0, 1, 2` to `a, b, c`."
  Hint (hidden := true) "[Hint m3bxs] Supply all four fields at once with
  `refine' \{ toFun := _, invFun := _, left_inv := _, right_inv := _ }`."
  refine' { toFun f := (f 0, f 1, f 2), invFun t := ![t.1, t.2.1, t.2.2], left_inv := _, right_inv := _ }
  · Hint (hidden := true) "[Hint v8rq2] Unfold `LeftInverse` and simplify."
    simp [LeftInverse]
    intro f
    Hint (hidden := true) "[Hint k3mwt] Two functions are equal as soon as they agree on every argument — that is `funext`."
    funext x
    Hint (hidden := true) "[Hint dz6pf] Only three values of `x` are possible; `fin_cases x` treats them one by one."
    fin_cases x
    · Hint (hidden := true) "[Hint n5hjb] Try `simp`."
      simp
    · simp
    · simp
  · Hint (hidden := true) "[Hint t7gks] Unfold `RightInverse` and `LeftInverse`, then simplify."
    simp [RightInverse, LeftInverse]

/- Already in the place introduce vector.-/
NewTactic refine' fin_cases

NewDefinition Equiv
-- TODO: fin_cases should be in set-theory
