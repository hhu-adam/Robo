
| Planet                        | new name | levels         | tried? | hints        | story  | summary | picture | desirable changes                                                                                |
|:------------------------------|:---------|:---------------|:-------|:-------------|:-------|:--------|:--------|:-------------------------------------------------------------------------------------------------|
| **Version 1.0:**              |          |                |        |              |        |         |         |                                                                                                  |
| Logos                         | ==       | +++            | +++    | +++          | +++    | +       | +++     | JE: DONE                                                                                         |
| Implis                        | ==       | +++            | +++    | +++          | ++     | +       | +++     | JE: DONE                                                                                         |
| Quantus                       | ==       | +++            | +++    | +++          | +++    | +       | +++     | JE: DONE                                                                                         |
| Spinoza                       | ==       | ++             | ++     | ++           | ++     |         | +++     |                                                                                                  |
| Luna                          | ==       | +              | +++    | +++          | update |         | +++     |                                                                                                  |
| Babylon                       | ==       | +              | +++    | +++          | +++    |         | +++     | TODO: introduce (Finset.)sum_subset  (for Robotswana L05)                                        |
| FunctionBij                   | Isos?    | +              | TODO   |              | TODO   |         | TODO    |                                                                                                  |
| FunctionInj                   | Monos?   | +              | TODO   |              | TODO   |         | TODO    |                                                                                                  |
| FunctionSurj                  | Epos?    | +              | +      |              | TODO   |         | TODO    |                                                                                                  |
| Cantor                        | ==       | ++             | +      | +            | +      |         | +++     |                                                                                                  |
| Robotswana                    | ==       | ++             | +      | update (L05) | update |         | +++     |                                                                                                  |
| SetTheory                     | Synolos  | TODO           |        |              |        |         |         | TODO: use set of primes in examples; introduce Finite; new Boss: set of primes is infinite                                                        |
| Prime                         | Atomos   | +              | TODO   | TODO         | TODO   |         | TODO    | (introduce ∃!) TODO: Boss: only even prime is 2 |
| GoodByePlanet                 | Ciao     | (done)         | (done) | (done)       | TODO   |         | +++     |                                                                                                  |
|                               |          |                |        |              |        |         |         |                                                                                                  |
| **Version 2.0:**              |          |                |        |              |        |         |         |                                                                                                  |
| SymmSquare                    | TODO     | o TODO: L08    | TODO   | TODO         | TODO   |         | TODO    |                                                                                                  |
| Quotient                      | TODO     | 7-?            | TODO   | TODO         | TODO   |         | TODO    |                                                                                                  |
| MatrixSpan                    | TODO     | o TODO: sorrys | TODO   | TODO         | TODO   |         | TODO    |                                                                                                  |
| RealUncountable               | TODO     | TODO .         | TODO   | TODO         | TODO   |         | TODO    |                                                                                                  |
|                               |          |                |        |              |        |         |         |                                                                                                  |
| **Possible future versions:** |          |                |        |              |        |         |         |                                                                                                  |
| Intervals; continuity         |          |                |        |              |        |         |         |                                                                                                  |
| ContinuousFunction            |          | TODO ..        |        |              |        |         |         |                                                                                                  |
| CosExtInequality              |          | TODO ...       |        |              |        |         |         |                                                                                                  |
|                               |          |                |        |              |        |         |         |                                                                                                  |
| **Trash:**                    |          |                |        |              |        |         |         |                                                                                                  |
| [[Tmp]]                       |          |                |        |              |        |         |         |                                                                                                  |
| [[VectorSpan]]                |          |                |        |              |        |         |         |                                                                                                  |
| [[NewStuff]]                  |          |                |        |              |        |         |         |                                                                                                  |
| [[Quantum]]                   |          |                |        |              |        |         |         |                                                                                                  |
                                                                   |

### Tactics

- recursive `constructor` -- some version of `refine`??
- we've thrown out `injection` tactic
- use `choose` instead of `obtain` for existential hypotheses

## FunctionBasics

#### L??: succ has left inverse, using if … then … else
Defining the left inverse as n ↦ n-1 (now in branch) looks ill-defined to a mathematician, so requires some explanation.

#### L?? BOSS: function which semiconjugates to successor function is surjective

**need to introduced `succ` here or elsewhere, or reformulate**

## FunctionSurj

Remove `NewTheorem congr_fun` from end of file.

#### L?? BOSS: TFAE definitions of surjectivity

**Remove TFAE and reference to image/preimage**


## FunctionImagePreimage

#### L??: injective → fibres are singletons
- ∃! needs to be explained -- perhaps already in Quantus? (see table above)
- Add hidden hint for `obtain`
- Add hint regarding overly complicated goal after `use a`:

  `(fun a => f a = b) a ∧ ∀ (y : A), (fun a => f a = b) y → y = a`

  `simp` turns this into

  `f a = b ∧ ∀ (y : A), f y = b → y = a`

  **Or can mathlib's `use` be improved??**

## FunctionBij

#### L02 BOSS: inverse of a bijection

Update hint on choose -- we should have already seen exactly how to do this in FunctionSurj.

My solution:
````
constructor
intro h
obtain ⟨ h_inj, h_surj⟩ := h
choose g hg using h_surj
use g
have h_r : RightInverse g f
assumption
constructor
unfold LeftInverse
intro a
apply h_inj
rw [hg]
assumption
intro h
obtain ⟨ g, hL, hR ⟩ := h
unfold RightInverse at hR
unfold LeftInverse at *
constructor
intro a a' h
apply congr_arg g at h
rw [hL] at h
rw [hL] at h
assumption
intro b
use (g b)
apply hR
````

# Potential Future Levels

#### Bij Future L03: A × A × A = (Fin 3 → A)

**currently unplayable (too many new concepts/too much new notation)**

#### Bij Future L04: Equiv (how to use it)

Need to discuss structures here, and explain what the different fields of Equiv are.

My solution:
````
rw [bijective_iff_has_inverse]  -- already known from L02
use f.invFun
constructor
apply f.left_inv
apply f.right_inv
````
This solution avoids introducing the new theorem `Equiv.injective`, and recycles L02.


#### Bij Future L05: Equiv (how to construct it)

Should come before L04, as it necessarily explains what the fields of Equiv are.

My solution:
````
rw [bijective_iff_has_inverse] at h
  choose g hL hR using h
  constructor
  · use f
  · use g
  · use hL
  · use hR
````

Note that we cannot start with:
````
rw [bijective_iff_has_inverse] at h
obtain ⟨g, hL, hR⟩ := h
````
But this fails, as explained [here](https://leanprover-community.github.io/mathlib4_docs//Init/Core.html#Exists).
