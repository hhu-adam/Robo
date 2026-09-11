import Game.Metadata

World "Symmetric Square"
Level 7

Introduction "Intro Symm L07"

open Function Sym Sym2 List

attribute [local instance] Sym2.Rel.setoid

variable {A B : Type*} {f : Sym2 A → B} {s : Setoid (A × A)} {a b : A}

Statement Sym_f {A B : Type*} : (Sym2 A → B) → (A → A → B) := by
  Hint "[Hint sy7res] Every function on unordered pairs can be read as a function of two
    separate arguments: send `a` and `b` to the value of `f` at the class of `(a, b)`.
    Building that function is the whole content of this level."
  let s := Sym2.Rel.setoid A
  intro f
  Hint "[Hint sy7cmp] Remember the previous levels: precomposing with the quotient map turns
    `{f}` into the function `{f} ∘ Quotient.mk s : A × A → B` on *ordered* pairs. Only the
    pair has to be split into its two entries now."
  Hint (hidden := true) "[Hint sy7cur] `Function.curry` takes a function of type `α × β → γ`
    to `α → β → γ` in a natural way."
  apply curry (f ∘ Quotient.mk s)

/--
`Sym_f f : A → A → B` reads a function `f : Sym2 A → B` on unordered pairs as a function of
two separate arguments:

```
Sym_f f a b = f ⟦(a, b)⟧
```
-/
DefinitionDoc Sym_f as "Sym_f" in "Quotient"

NewDefinition Function.curry Sym_f
