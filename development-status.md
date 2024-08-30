
| Planet                 | new name   | levels         | tried? | hints  | story  | summary    | picture     | desirable changes                                                                                     |
|:-----------------------|:-----------|:---------------|:-------|:-------|:-------|:-----------|:------------|:------------------------------------------------------------------------------------------------------|
| Logos                  | ==         | +++            | +++    | +++    | +++    | +          | +++         |  JE: DONE                                                                                             |
| Implis                 | ==         | +++            | +++    | +++    | ++     | +          | +++         |  JE: DONE                                                                                             |
| Quantus                | ==         | +++            | +++    | +++    | +++    | +          | +++         | TODO: add ∃! ?                                                                                        |
| Spinoza                | ==         | ++             | ++     | ++     | ++     |            | +++         | TODO: add TFAE tactics (used in boss of FunctionSurj)                                                 |
| Luna                   | ==         | +              | +++    | +++    | +++    |            | +++         | TODO: level explaining `obtain h_lt \| h_eq \| h_gt := lt_trichotomy a b` (needed in FunctionInj L04) |
| Babylon                | ==         | +              | +++    | +++    | +++    |            | +++         | TODO: add sum over zeroes, adding over singleton                                                      |
| FunctionBij            | Isos?      | +              | TODO   |        | TODO   |            | TODO        | remove linear_combination                                                                             |
| FunctionInj            | Monos?     | +              | TODO   |        | TODO   |            | TODO        |                                                                                                       |
| FunctionSurj           | Epos?      | +              | +      |        | TODO   |            | TODO        |                                                                                                       |
| Cantor                 | ==         | ++             | +      | +      | +      |            | +++         | move first problem somewhere else                                                                     |
| MatrixSpan             | TODO       | o TODO: sorrys | TODO   | TODO   | TODO   |            | TODO        |                                                                                                       |
| Robotswana             | ==         | ++             | +      | update | update |            | +++         |                                                                                                       |
| SetTheory              | Synolos    | TODO           |        |        |        |            | ??          | (add intervals?? -- only necessary for analysis)                                                      |
| ~FiniteSetTheory       | TODO       | TODO           |        |        |        |            | TODO        |                                                                                                       |
| SymmSquare             | TODO       | o TODO: L08    | TODO   | TODO   | TODO   |            | TODO        |                                                                                                       |
| Quotient               | TODO       | 7-?            | TODO   |        | TODO   |            | TODO        |                                                                                                       |
| Prime                  | TODO       | +              | TODO   | TODO   | TODO   |            | TODO        |                                                                                                       |
| ? RealUncountable      | TODO       | TODO .         |        |        |        |            |             |                                                                                                       |
| GoodByePlanet          |            | TODO (.)       |        |        |        |            | Spacecraft? |                                                                                                       |
|                        |            |                |        |        |        |            |             |                                                                                                       |
| [[[Continuity]]]       |            |                |        |        |        |            |             |                                                                                                       |
| [[ContinuousFunction]] |            | TODO ..        |        |        |        |            |             |                                                                                                       |
| [[CosExtInequality]]   |            | TODO ...       |        |        |        |            |             |                                                                                                       |
|                        |            |                |        |        |        |            |             |                                                                                                       |
| [[Tmp]]                |            |                |        |        |        |            |             |                                                                                                       |
| [[VectorSpan]]         |            |                |        |        |        |            |             |                                                                                                       |
| [[NewStuff]]           |            |                |        |        |        |            |             |                                                                                                       |
| [[Quantum]]            |            |                |        |        |        |            |             |                                                                                                       |

### Tactics

- recursive `constructor` -- some version of `refine`??
- we've thrown out `injection` tactic

### FunctionSurj

nice levels: L12_Surjective, L15_Surjective_TFAE

### FunctionInj

#### L02
'trivial' comes a bit unexpected. My solution:
````
unfold Injective
push_neg
use 2, 3
-- trivial closes the goal in the sample solution!  Add hint about this?
constructor
simp [f]
have : ¬ Even 3
rw [← Nat.odd_iff_not_even]
use 1
ring
rw [if_neg this]
simp
````

#### L03

- ∃! needs to be explained -- perhaps already in Quantus? (see table above)
- add hidden hint for `obtain`
- add hint regarding overly complicated goal after `use a`:

  `(fun a => f a = b) a ∧ ∀ (y : A), (fun a => f a = b) y → y = a`

  `simp` turns this into

  `f a = b ∧ ∀ (y : A), f y = b → y = a`


#### L04: prove that StrictMono is injective

- anonymous variables
- trick `obtain h_lt | h_eq | h_gt := lt_trichotomy a b` needs to be explained on Luna (see table above)
- introduces PreOrders and LinearOrders -- would ONE of these suffice?
- Why does linarith not find contradiction from
  ````
  h: f a = f a'
  hlt: f a < f a'
  ````
  ? And why not even from
  ````
  hlt: f a' < f a'
  ````
  ? Why does `simp` work?

  Again, all of this should ideally be explained on Luna!

#### L05: use the fact that StrictMono is injective
  Perhaps swap L04 and L05 (L05 is the easier level, and motivates L04)

  Both L04 and L05 could be move closer to levels about ‘existence of left inverse implies injectivity`.

#### L06: succ has left inverse
Nice level. Should be closer to L09 and L11.

Defining the left inverse as n ↦ n-1 looks ill-defined to a mathematician, so this requires a hint.
My solution was:
````
let g : ℕ → ℕ := fun n ↦ if n = 0 then 0 else n - 1
use g
intro n
by_cases h : n = 0
rw [h]
simp [g]
simp [g]
````
This solution currently triggers three warnings
- `The tactic 'if' is not available in this game!`,
- `The tactic 'then' is not available in this game!`,
- `The tactic 'else' is not available in this game!`,

#### L07: extending a function from ℕ to ℤ
Not sure about this level.

- wrong title (This is not about left inverses.)
- anonymous assumption
- needs `Int.toNat`  – ideally, this would be explained somewhere where we (already?) discuss well-definedness in lean/mathlib
- Current solution needs multiline tactics.
  My solution:
  ````
  have a : A := Classical.arbitrary A
  let g : ℤ → A := fun n ↦ if n ≥ 0 then f (Int.toNat n) else a
  use g
  intro n
  have h : n ≥ 0
  simp
  simp [g]
  ````
- `Classical.arbitrary` should be replaced by `Classical.choice` once assumption `Nonempty A` has a name.
- Again, need to unlock `if`, `then`, `else`.

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

- **causes server to crash**
- summary in introduction is wrong
- `have` statement is superfluous; instead can just do:
````
intro a
apply injf
rw [hL]
````

#### L11: most injections have left inverses

- **does not compile in web editor** (error `failed to synthesize Decidable (…)`)
- **solution looks complicated, not possible to guess from previous levels!**
- still uses `choose_spec`, which we were trying to eliminate by using the `choose` tactic

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
