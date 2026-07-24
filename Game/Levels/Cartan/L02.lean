import Game.Metadata

World "Cartan"
Level 2

open Filter Topology FullGrind

Introduction "
Can think of filters as generalized points.
`ℝ` has many filters other than `𝓝 a`.
The filter `atTop` on ℝ is the generalized point 'at infinity': a set belongs to
`atTop` when it contains every sufficiently large number, i.e. when it is a
neighborhood of `+∞`'.

In this level you prove that the *open* ray beyond `b` is also a
neighborhood of `+∞`.
"

/---/
TheoremDoc Filter.mem_atTop as "mem_atTop" in "Filter"

/- The open ray beyond `b` is a neighborhood of `+∞`. -/
open FullGrind in
Statement {b : ℝ} : {x : ℝ | b < x} ∈ atTop := by
  Hint (strict := true) "[Hint pkzt] By `Filter.mem_atTop`, the ray `\{x | b + 1 ≤ x}` belongs to
  `atTop`.  Show this first."
  Branch
    have : {x : ℝ | b + 1 ≤ x} ∈ atTop := by
      apply mem_atTop
    Hint "Second filter axiom says filter is upward closed (`Filter.mem_of_superset`)." -- A
  Branch
    have : {x : ℝ | b ≤ x} ∈ atTop := by
      Hint "[Hint ht1zj] This statement is correct, but it won't help you."
      apply mem_atTop
  obtain h := (mem_atTop (b + 1))
  Hint "Second filter axiom says filter is upward closed (`Filter.mem_of_superset`)."  -- A
  apply mem_of_superset h
  grind

/- NOTE
I don't understand why the first branch above is necessary.
The two identical hints marked -- A are placed in identical proof states,
so the hint in the main solution should trigger when user enters the alternative
solution recorded in the branch.  But somehow this doesn't happen :(

In the following minimal example, everything works as expected:
```
Statement {A B : Prop} (hA : A ∧ A) (hB : B) : B := by
  obtain h := hA.left
  Hint "A"
  exact hB
```
In this minimal example, Hint "A" *does* show up when I enter the following alternative solution
in the browser:
```
  have : A
  apply hA.1
```

TODO:  Find a minimal example of the above behaviour and file a bug report for lean4game.
-/

Conclusion "Conclusion Cartan L02: Any other filter axioms?  Yes, filter is non-empty.
Equivalently, it contains `univ` (`Filter.univ_mem`)."

NewTheorem Filter.mem_atTop
NewDefinition Filter.atTop
