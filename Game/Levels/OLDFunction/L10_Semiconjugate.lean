import Game.Metadata

World "Function"
Level 10

Title "Semiconjugate"
Introduction
"
We say that `f : α → β` semiconjugates `g : α → α` to `g' : β → β` if

```
f ∘ g = g' ∘ f
```

We use `∀ x, f (ga x) = gb (f x)` as the definition, so given `h : Function.Semiconj f ga gb` and
`a : α`, we have `h a : f (ga a) = gb (f a)` and `h.comp_eq : f ∘ ga = gb ∘ f`.
"

open Function Nat


Statement {f : α → ℕ} {z : α} (h : f z = 0) {g : α → α}
    (hs : Semiconj f s succ) : Surjective f := by
  intro n
  induction n with n hn
  · use z
  · rcases hn with ⟨a, ha⟩
    use s a
    Hint "
        you can rewrite along the equality `hs`. "
    rw [hs]
    rw [ha]
