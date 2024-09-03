
| Planet                 | new name | levels         | tried? | hints  | story  | summary | picture | desirable changes                                                                                     |
|:-----------------------|:---------|:---------------|:-------|:-------|:-------|:--------|:--------|:------------------------------------------------------------------------------------------------------|
| Logos                  | ==       | +++            | +++    | +++    | +++    | +       | +++     | JE: DONE                                                                                              |
| Implis                 | ==       | +++            | +++    | +++    | ++     | +       | +++     | JE: DONE                                                                                              |
| Quantus                | ==       | +++            | +++    | +++    | +++    | +       | +++     | JE: DONE                                                                                              |
| Spinoza                | ==       | ++             | ++     | ++     | ++     |         | +++     | TODO: add TFAE tactics (used in boss of FunctionSurj)                                                 |
| Luna                   | ==       | +              | +++    | +++    | update |         | +++     |                                                                                                       |
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
| Prime                  | TODO     | +              | TODO   | TODO   | TODO   |         | TODO    | TODO: introduce ∃!                                                                                    |
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

## FunctionSurj

nice levels: L12_Surjective, L15_Surjective_TFAE

## FunctionInj

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

## FunctionBij

#### L01 - similar to Inj L06: succ has left inverse
````
simp [f] at hab -- TODO: is there a better way?
````

can be simplified to

````
simp f
````

#### L02: inverse of a bijection

**looks more like a boss level – quite involved!**

Update hint on choose -- we should have already seen exactly how to do this in FunctionSurj.

The hint "something about the fact that ` ∀ (b : B), f (g b) = b` implies {g} is a right inverse of {f}. We use this in the next step to prove {g} is also a left inverse of {f}."
should be rather be something along the lines of:
"Zeig erst einmal RightInverse g f, also zum Beispiel `have hR : RightInverse g f`"

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

#### L03

**unplayable**

**needs fconstructor**

#### L04: Equiv (how to use it)

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


#### L05: Equiv (how to construct it)

Should perhaps come before L04, as it necessarily explains what the fields of Equiv are.

Probably needs **exact** in any case.

I would like to start with:
````
rw [bijective_iff_has_inverse] at h
obtain ⟨g, hL, hR⟩ := h
````
But this fails:
````
tactic 'cases' failed, nested error:
tactic 'induction' failed, recursor 'Exists.casesOn' can only eliminate into Prop
````

**can we somehow avoid `fconstructor`??**

#### L06: Equiv curry/uncurry

This really needs **exact** for the nice solution.


#### L07:

After
````
unfold Surjective
push_neg
````
the two sides of the equivalence are almost identical! Perhaps modify question so that they *are* identical?
