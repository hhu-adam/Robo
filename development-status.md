
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

#### L12: SEMIBOSS function which semiconjugates to successor function is surjective

Good application of induction!

**need to introduced `succ` here or elsewhere, or reformulate**

Remove `NewTheorem congr_fun` from end of file.

#### L13: surjective ↔ range = univ

#### L14: non-empty fibres → ∃ right inverse


#### L15: BOSS TFAE definitions of surjectivity

Uses `Set.Nonempty`, which we've recently purged in L14.

**The part `surjective  ↔ non-empty fibres` is used in Boss of FunctionBij**!


## FunctionInj

#### L03 injective → fibres are singletons
- ∃! needs to be explained -- perhaps already in Quantus? (see table above)
- Add hidden hint for `obtain`
- Add hint regarding overly complicated goal after `use a`:

  `(fun a => f a = b) a ∧ ∀ (y : A), (fun a => f a = b) y → y = a`

  `simp` turns this into

  `f a = b ∧ ∀ (y : A), f y = b → y = a`

  **Or can mathlib's `use` be improved??**

#### L04: StrictMono → injective

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

Remove `NewTactic trans` at the end of the file!

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

#### L03: A × A × A = (Fin 3 → A)

**unplayable**

**needs fconstructor**

**remove?** 

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

#### L07: Reading exercise for A → B → C

A tiny variation can be solved in just three lines:
````
example (f : ℕ → A → B) : ¬ Surjective f ↔ ∃ g : A → B, ∀ n, f n ≠ g := by
  unfold Surjective
  push_neg
  rfl
````
Can the actual question be solved similarly, in four lines perhaps? 
Or should we change the question?

#### L08: Diagonal injective

Set.preimage has not been introduced.

Hopefully, `Fin n` will be explained elsewhere.


#### L09: Boss – f surjective ↔ f⁻¹ injective 

My own solution was rather long:
````
example {A B : Type} {f : A → B} : Injective (preimage f) ↔ Surjective f := by
  constructor
  · intro h_inj
    intro b 
    by_contra h_contra
    push_neg at h_contra
    have h₁ : preimage f ∅ = ∅ := by
      simp
    have h₂ : preimage f {b} = ∅ := by 
      rw [eq_empty_iff_forall_not_mem]
      intro a
      have h'a := h_contra a
      assumption
    have : preimage f ∅ = preimage f {b}  
    rw [h₁,h₂]
    apply h_inj at this
    symm at this
    rw [eq_empty_iff_forall_not_mem] at this
    apply this b
    simp
  · intro h_surj
    intro s s' hs
    ext b 
    constructor
    · intro hx
      unfold Surjective at h_surj
      obtain ⟨y, hy⟩  := h_surj b
      have : y ∈ f ⁻¹' s := by 
        simp
        rw [← hy] at hx
        assumption
      rw [hs] at this
      simp at this
      rw [hy] at this
      assumption
    · intro hx
      unfold Surjective at h_surj
      obtain ⟨y, hy⟩  := h_surj b
      have : y ∈ f ⁻¹' s' := by 
        simp
        rw [← hy] at hx
        assumption
      rw [← hs] at this
      simp at this
      rw [hy] at this
      assumption
````

The first part of the shorter sample solution seems to depend quite crucially on the `change` tactic, which we haven't introduced.
It might be useful to have one part of the Boss level of FunctionInj available here, namely:

````
lemma surjective_iff_nonempty_fibres {A B : Type} (f : A → B) : Surjective f ↔ ∀ b : B, ∃ (a : A), a ∈ (f ⁻¹' { b }) := by
  sorry
````

But I haven't managed to find a more satisfactory solution by assuming this lemma.
the two sides of the equivalence are almost identical! Perhaps modify question so that they *are* identical?

The second part can be solved more elegantly using
````
Function.Surjective.image_preimage.{u_1, u_2} {α : Type u_1} {β : Type u_2} {f : α → β} (hf : Surjective f)
  (s : Set β) : f '' (f ⁻¹' s) = s
````
Using this theorem, which could be a separate exercise in FunctionSurj, the second half above becomes:
````
· intro h_surj
  intro s s' hs
  apply congr_arg (image f) at hs
  rw [h_surj.image_preimage] at hs
  rw [h_surj.image_preimage] at hs
  assumption
````


## Reordering??


#### Surj 01:
**fun ↦**
  
#### Surj 02:
fun ↦ 

#### Surj 03:
**let**
**comp_apply**

#### Surj 04:
**if…then…else**
**if_pos** **if_neg**

let
comp_apply

#### Surj 05:
**funext**

#### Surj 06:
**congr_arg**

#### Surj 07: 
**congr_fun**
 
#### Surj 08: direct “definition” of RightInverse
**RightInverse**

congr_fun

#### Surj 09: mathlib definition of RightInverse in terms of LeftInverse
**LeftInverse**
    
RightInverse
 
#### Surj 10: concrete right inverse
**HasRightInverse**1


#### Surj 11: concrete function surjective
**Surjective**

#### Surj 12 SEMIBOSS: function which semiconjugates to successor function is surjective

congr_fun

induction

#### Surj 13: surjective ↔ range = univ
**range** 
**mem_range**

#### Surj 14: non-empty fibres → ∃ right inverse
**choose**

**preimage**

#### Surj 15: BOSS TFAE definitions of surjectivity
choose
HasRightInverse
Surjective

#### Inj 01: concrete function injective
**Injective**
  
#### Inj 02: concrete function not injective
if … then … else

Injective

#### Inj 03: injective → fibres are singletons
range 
Injective
    
#### Inj 04: how to use Equiv 
**Equiv**
  
#### Inj 05: how to construct Equiv
**Equiv**

RightInverse

#### Inj 04: StrictMono → injective – proof
**StrictMono**
   
Injective

#### Inj 05: application of StrictMono → application

#### Inj 06: succ has left inverse
**HasLeftInverse**

succ

if … then … else
  
#### Inj 07a & b: extend from ℕ to ℤ
if … then … else

#### Inj 08: image of self vs preimage of LeftInverse
**image**

preimage
LeftInverse
congr_arg
   
#### Inj 09: HasLeftInverse → Injective

HasLeftInverse
LeftInverse
congr_arg
   
#### Inj 10
LeftInverse
RightInverse
Injective

#### Inj 11: Injective → HasLeftInverse
range

choose
arbitrary

#### Bij 01
**Bijective**

#### Bij 02 ?BOSS?  inverse of a bijection

LeftInverse
RightInverse
Bijective
choose

#### [Bij 03 A × A × A = (Fin 3 → A)]

#### Bij 04 Equiv (how to use it)

**depends on Bij 02**

RightInverse
LeftInverse
Surjective
Injective
congr_arg
…?…

#### Bij 05 Equiv (how to construct it)

RightInverse
LeftInverse
Surjective
Injective


#### Bij 06 Equiv curry/uncurry
**curry_uncurry** **uncurry_curry**

#### Bij 07 Reading exercise for A → B → C
Surjective
[curry]

#### Bij 08 Diagonal injective
Injective
congr_fun
[curry]
Fin n

#### Bij 09*: Surjective.image_preimage
Surjective
Image
Preimage

#### Bij 09 BOSS – f surjective ↔ f⁻¹ injective 
Surjective
Injective
Image
Preimage
fibre

