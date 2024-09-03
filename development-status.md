
| Planet                 | new name | levels         | tried? | hints  | story  | summary | picture | desirable changes                                                                                     |
|:-----------------------|:---------|:---------------|:-------|:-------|:-------|:--------|:--------|:------------------------------------------------------------------------------------------------------|
| Logos                  | ==       | +++            | +++    | +++    | +++    | +       | +++     | JE: DONE TODO: TacticDoc `decide`.                                                                                            |
| Implis                 | ==       | +++            | +++    | +++    | ++     | +       | +++     | JE: DONE                                                                                              |
| Quantus                | ==       | +++            | +++    | +++    | +++    | +       | +++     | (add ∃! ? -- see Prime planet);  TODO: replace L05 by `decide`  (eg: prove that 5 is odd or 8 is even)                            |
| Spinoza                | ==       | ++             | ++     | ++     | ++     |         | +++     | TODO: add TFAE tactics (used in boss of FunctionSurj)                                                 |
| Luna                   | ==       | +              | +++    | +++    | +++    |         | +++     | TODO: level explaining `obtain h_lt \| h_eq \| h_gt := lt_trichotomy a b` (needed in FunctionInj L04) |
| Babylon                | ==       | +              | +++    | +++    | +++    |         | +++     | TODO: add sum over zeroes, adding over singleton                                                      |
| FunctionBij            | Isos?    | +              | TODO   |        | TODO   |         | TODO    | remove linear_combination                                                                             |
| FunctionInj            | Monos?   | +              | TODO   |        | TODO   |         | TODO    |                                                                                                       |
| FunctionSurj           | Epos?    | +              | +      |        | TODO   |         | TODO    |                                                                                                       |
| Cantor                 | ==       | ++             | +      | +      | +      |         | +++     | move first problem somewhere else                                                                     |
| MatrixSpan             | TODO     | o TODO: sorrys | TODO   | TODO   | TODO   |         | TODO    |                                                                                                       |
| Robotswana             | ==       | ++             | +      | update | update |         | +++     |                                                                                                       |
| SetTheory              | Synolos  | TODO           |        |        |        |         | ??      | (add intervals?? -- only necessary for analysis)                                                      |
| ~FiniteSetTheory       | TODO     | TODO           |        |        |        |         | TODO    |                                                                                                       |
| SymmSquare             | TODO     | o TODO: L08    | TODO   | TODO   | TODO   |         | TODO    |                                                                                                       |
| Quotient               | TODO     | 7-?            | TODO   |        | TODO   |         | TODO    |                                                                                                       |
| Prime                  | TODO     | +              | TODO   | TODO   | TODO   |         | TODO    | TODO: introduce ∃!                                                                      |
| ? RealUncountable      | TODO     | TODO .         |        |        |        |         |         |                                                                                                       |
| GoodByePlanet          |          | TODO (.)       |        |        |        |         | +++     | JE: added empty `End` planet                                                                          |
|                        |          |                |        |        |        |         |         |                                                                                                       |
| [[[Continuity]]]       |          |                |        |        |        |         |         |                                                                                                       |
| [[ContinuousFunction]] |          | TODO ..        |        |        |        |         |         |                                                                                                       |
| [[CosExtInequality]]   |          | TODO ...       |        |        |        |         |         |                                                                                                       |
|                        |          |                |        |        |        |         |         |                                                                                                       |
| [[Tmp]]                |          |                |        |        |        |         |         |                                                                                                       |
| [[VectorSpan]]         |          |                |        |        |        |         |         |                                                                                                       |
| [[NewStuff]]           |          |                |        |        |        |         |         |                                                                                                       |
| [[Quantum]]            |          |                |        |        |        |         |         |                                                                                                       |

### Tactics

- recursive `constructor` -- some version of `refine`??
- we've thrown out `injection` tactic

### FunctionSurj

nice levels: L12_Surjective, L15_Surjective_TFAE

### FunctionInj

#### L02

**Introduce `decide` in Prime planet.**

#### L03
- ∃! needs to be explained -- perhaps already in Quantus? (see table above)
- Add hidden hint for `obtain`
- Add hint regarding overly complicated goal after `use a`:

  `(fun a => f a = b) a ∧ ∀ (y : A), (fun a => f a = b) y → y = a`

  `simp` turns this into

  `f a = b ∧ ∀ (y : A), f y = b → y = a`

  **Or can mathlib's `use` be improved??**

#### L04: prove that StrictMono is injective

Trick `obtain h_lt | h_eq | h_gt := lt_trichotomy a b` needs to be explained on Luna (see table above)

#### L05: use the fact that StrictMono is injective
Perhaps swap L04 and L05 (L05 is the easier level, and motivates L04)
    
Both L04 and L05 could be move closer to levels about ‘existence of left inverse implies injectivity`.

#### L06: succ has left inverse, using if … then … else
Nice level. Should be closer to L09 and L11.

Defining the left inverse as n ↦ n-1 (now in branch) looks ill-defined to a mathematician, so requires some explanation.

#### L07: extending a function from ℕ to ℤ, using if … then … else
Give `Int.toNat` as a hint.

**turn more difficult version into additional level!**

#### L08: image versus preimage
Good, but sightly out of context. My solution:
````
intro b hb
obtain ⟨a,ha,h⟩ := hb
unfold LeftInverse at hL
apply congr_arg g at h
have hLa := hL a
rw [← hLa, h] at ha
assumption
````
In short:
- `dsimp` in the sample solution should be `unfold`
- I've used the opportunity to apply `congr_arg … at`

#### L09: existence of left inverse implies injectivity
No need to introduce `trans` *here*:
````
intro a a' ha
obtain ⟨ g, hg⟩ := h
apply congr_arg g at ha
unfold LeftInverse at hg
rw [hg a, hg a'] at ha
assumption
````
(It's anyway been introduced ealier, so current solution can be left as a branch.)

#### L10: left inverse of injection is also right inverse

#### L11: most injections have left inverses

My solution:
````
  have a₀ : A := Classical.arbitrary A
  have : ∀ b : B, ∃ a : A, b ∈ range f → f a = b := by
    intro b
    by_cases hb : b ∈ range f
    obtain ⟨a,ha⟩ := hb
    use a
    intro h
    assumption
    use a₀
    intro h
    contradiction
  choose g hg using this
  use g
  intro a
  apply hf
  apply hg
  simp
````
Perhaps the `have` statement should be a separate previous level, which then needs to be retyped verbatim in the boss level.
