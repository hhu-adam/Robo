import GameServer.Commands

/-! ## Definitions -/


/- ABBILDUNGEN -/

/--
A mapping `f` is injectiv, if:

```
∀ a b, f a = f b → a = b
```
-/
DefinitionDoc Function.Injective as "Injective" in "Fun"


/--
A mapping `f` is surjectiv, if:

```
∀ b, ∃ a, f a = b
```
-/
DefinitionDoc Function.Surjective as "Surjective" in "Fun"


/--
A mapping ist bijectiv, if it is injektiv and surjektiv.
-/
DefinitionDoc Function.Bijective as "Bijective" in "Fun"


/--
A mapping `f` is strictly monotonous, if:

```
∀ ⦃a b⦄, a < b → f a < f b
```
-/
DefinitionDoc StrictMono as "StrictMono" in "Fun"


/-- `Function.RightInverse f g` is defined as `LeftInverse g f`.
In other words: `∀ x, g (f x) = x`.

You have to write `Function.RightInverse`  instead of `RightInverse`,
as `RightInverse` is ambigous in Leanic.
-/
DefinitionDoc Function.RightInverse as "RightInverse" in "Fun"
-- Note the fact that one sees `LeftInverse` but `Function.RightInverse` is because
-- some mathlib init-file defines `_root_.RightInverse`. mathlib4#11415 investigates this.


/--
`LeftInverse g f` means `g ∘ f = id`, or more exactly:
`∀ x, g (f x) = x`, as can be seen with `unfold`.
-/
DefinitionDoc Function.LeftInverse as "LeftInverse" in "Fun"


/--
`HasRightInverse f` means, that `f` has a right inverse.

`HasLeftInverse f` means, that `f` has left inverse.
-/
DefinitionDoc Function.HasRightInverse as "Has…Inverse" in "Fun"


/--
For a self-mapping `f : A → A` and an element `a : A`, `IsFixedPt f a` is the expression `f a = a`.
Look up definition with `unfold IsFixedPt`.
-/
DefinitionDoc Function.IsFixedPt as "IsFixedPt" in "Fun"

/--
For a mapping `f : A → A`, `fixedPoints f : Set A` is the set of fixed points of `f `.
Look up definition with `unfold fixedPoints`.
-/
DefinitionDoc Function.fixedPoints as "fixedPoints" in "Fun"

/--
For two subsets `A` and `B` of `S` (i.e. `A B : Set S`), `A ∪ B` is their union.
`∪` is written as `\\union`.
-/
DefinitionDoc Set.union as "∪" in "Set"

/--
For two subsets `A` and `B` of `S` (i.e. `A B : Set S`), `A ∩ B` is their intersection.
`∩` is written as `\\inter`.
-/
DefinitionDoc Set.inter as "∩" in "Set"

/--
For a mapping `f : A → B`, `range f` is the full image set of `f`:
```
range f = {f a | a : A}
        = {  b | ∃ a, f a = b}
```
Is a diffierent notation for `f '' univ`.
`mem_range` is useful to work with it:
```
x ∈ range f ↔ ∃ a, f a = b
```
-/
DefinitionDoc Set.range as "range" in "Set"

/--
For a mapping `f : A → B`, `image f : Set A → Set B`
is one of the induced mappings on the power sets –
it maps a subset of `A` to the image `f '' A` of this subset under `f`.
-/
DefinitionDoc Set.image as "image" in "Set"

/--
For a mapping `f : A → B`, `preimage f : Set B → Set A`
is one of the induced mappings on the power sets –
it maps a subset of `B` to the preimage `f ⁻¹' A` of this subset under `f`.
-/
DefinitionDoc Set.preimage as "preimage" in "Set"


/--
For a mapping `f : A → B` and a subset `S` of `A`,
```
f '' S = {f a | a ∈ S} = {b | ∃ a ∈ S, f a = b}
```
is its image under `f`.  Note the space between `f` and `''`.
-/
DefinitionDoc Set.fimage as "f ''" in "Set"

/--
For a mapping `f : A → B` and a subset `T` of `B`,
```
f ⁻¹' T = { a | f a ∈ T}
```
is its preimage under `f`.
You write this as `f \-1'`.
Note the space between `f` and `\-1'`.
-/
DefinitionDoc Set.fpreimage as "f ⁻¹'" in "Set"

/--
The notation `fun x ↦ _` is used to define “anonymous functions.”
For example, `fun (x : ℤ) ↦  -x` defines the negation `ℤ → ℤ` without giving it a name.
You write the arrow `↦` as `\maps` or `\mapsto`.
Alternatively, instead of `↦` you can use `=>`.
-/
DefinitionDoc Symbol.function as "fun x ↦ _" in "Fun"


/- MENGEN -/

/--
`A : Set T` means that `A` is a subset of `T`
(or, more precisely, that `A` is a set consisting of elements of type `T`).
-/
DefinitionDoc Set as "Set" in "Set"

/--
For a subset `A : Set T` and an element `a` from `T` (more precisely: of type `T`), `a ∈ A` means that
`a` is in `A`.
For subsets of the form `A = { a : T | P a }`, you can simplify the statement
`a ∈ A` with `simp` to `P a`.
-/
DefinitionDoc Mem as "∈" in "Set"

/--
For a predicate `P : T → Prop`, `{ a : T | P a } : Set P` is the subset
consisting of all elements that satisfy the predicate.  For example,
```
{ n : ℕ | Even n }
```
is the set of even natural numbers.
You can simplify the statement `a ∈ { a : T | P a }`, using `simp`, to `P a` .
-/
DefinitionDoc setOf as "{·|·}" in "Set"

/--
For two subsets `(A B : Set T)`, `A\B` is the difference between `A` and `B`,
consisting of all elements of `A` that are not in `B`.
-/
DefinitionDoc SDiff as "·\\·" in "Set"

/--
For `A B : Set T`, `A ⊆ B` means that `A` is contained in `B`.

With `rw [subset_iff]`, you can rewrite `A ⊆ B` as `∀ x, x ∈ A → x ∈ B`.

If `A ⊆ B` is the proof goal, you can also directly use `intro a ha`
to select an element `a` with `ha : a ∈ A` (and then show `a ∈ B`).

If `h : A ⊆ B` is an assumption and an element `a` with `ha : a ∈ A` is given,
you can use `have hb := h ha` to obtain the statement `hb : a ∈ B`.

You write `⊆` as `\subset`.
-/
DefinitionDoc Subset as "⊆" in "Set"

/--
`∅ : Set T` is the empty subset.
In the Formaloverse `∅ : Set ℕ` is something different than `∅ : Set ℝ`
– one is a subset of ℕ, the other is a subset of ℝ!

With `rw [eq_empty_iff_forall_not_mem]` you translate the equation `S = ∅` into the
statement `∀ (x : T), x ∉ s`.

`∅` is written as `\emptyset`.
-/
DefinitionDoc Set.empty as "∅" in "Set"

/--
`univ : Set T` is the “subset” consisting of *all* elements of type `T`.

With `rw [eq_univ_iff_forall]`, you convert an equation of the form `S = univ` into the
statement `∀ (x : T), x ∈ S`.
-/
DefinitionDoc Set.univ as "univ" in "Set"

/--
For a finite subset `A : Finset T` and an element `a : T`,
`insert a A` is another way of writing `A ∪ {a}`.
If `a` is already in `A`, then obviously `insert a A = A`.
-/
DefinitionDoc Finset.insert as "insert" in "Finset"

/--
For a finite subset `A : Finset T` and an element `a : T`,
`erase A a` is another way of writing `A \ {a}`.
If `a` is not in `A` at all, then obviously `erase A a = A`.
-/
DefinitionDoc Finset.erase as "erase" in "Finset"

/--
For a finite subset `A : Finset T`, `card A : ℕ` is the cardinality of `A`,
i.e., the number of elements in `A`.
-/
DefinitionDoc Finset.card as "card" in "Finset"

/--
For `n : ℕ`, `Fin n` is the set $\{0, \dots, n-1\}$.

(`Fin n` is to be distinguished from `Icc 0 (n-1)`:
`Fin n` is a set, or more precisely a type, i.e. `Fin n : Type`,
whereas `Icc 0 (n-1) : Finset ℕ` is a finite subset of `ℕ`.)
-/
DefinitionDoc Fin as "Fin"

/--
`Icc a b` is the closed interval $[a,b]$.
-/
DefinitionDoc Finset.Icc as "Icc"
-- DefinitionDoc Disjoint as "Disjoint"
-- "
-- "

/--
`Nonempty T` means that an element in `T` (“of type `T`”) exists.
If `h : Nonempty T` is given as an assumption, we obtain an element `t : T` with `obtain ⟨t⟩ := h`.
Conversely, if we already have an element `t : T` given or constructed,
we can prove `Nonempty T` with `use t`.

Similarly, for a subset `A : Set T`, the statement `Nonemty A` is defined as `∃ x, x ∈ A`.
In this case, you can easily check this with `unfold Nonempty`.
-/
DefinitionDoc Nonempty as "Nonempty"
/-
Note that in reality there's a distinction between `Nonempty` (for types) and `Set.Nonempty` (for sets)

example (T : Type) : Nonempty T ↔ ∃ t : T, true := by
  -- unfold Nonempty  -- fails
  constructor
  · intro h
    obtain ⟨t⟩ := h
    use t
  · intro h
    obtain ⟨t, ht⟩ := h
    use t


example {TT : Type} (T : Set TT) : Set.Nonempty T ↔ ∃ t : TT, t ∈ T := by
  unfold Set.Nonempty -- optional
  constructor
  · intro h
    obtain ⟨t⟩ := h
    use t
  · intro h
    obtain ⟨t, ht⟩ := h
    use t

example {TT : Type} (T : Set TT) : Set.Nonempty T ↔ ∃ t : TT, t ∈ T := by
  rfl
-/

/--
For a subset `A : Set T`, `Set.Finite A` means that `A` has only a finite number of elements.
If `h : Set.Finite A` is given as an assumption, then `h.toFinset : Finset T` is the same subset `A`,
but now explicitly understood as a finite subset.
-/
DefinitionDoc Set.Finite as "Set.Finite" in "Set"


/- LOGIK -/

/--
`(A : Prop)` is any statement, without further specification as to whether it is true, false, or
unprovable.

See also `(True : Prop)` and `(False : Prop)` for the unconditionally true and false
statements, respectively.
-/
DefinitionDoc «Prop» as "Prop" in "Logic"

/--
`A ∧ B` (“and”) is the statement that both `A` and `B` are true.

## `A ∧ B` as a proof goal

The tactic `constructor` allows you to prove the two sub-statements `A` and `B` individually.

## `A ∧ B` as an assumption

With `obtain ⟨h₁, h₂⟩ := h`, you break down an assumption of the form `h : A ∧ B`
into its components `h₁ : A` and `h₂ : B`.
-/
DefinitionDoc And as "∧" in "Logic"

/--
`A ∨ B` (“or”) is the statement that at least one of the statements `A`, `B` is true.

## `A ∨ B` as proof goal

You can use the tactics `left` or `right` to decide
which statement you want to prove.

## `A ∨ B` as an assumption

Since you do not know which of the statements `A` or `B` you can assume,
you may have to show the proof goal twice:
once under the assumption `A` and once under the assumption `B`.
To do this, use the tactic
```
obtain h | h := h
```
-/
DefinitionDoc Or as "∨" in "Logic"

/--
For `A B : Prop`, `A → B` is the implication “`A` implies `B`.”
For other `X Y : Type`, `X → Y` is a mapping that maps values from `X` to `Y`.

## Implication as proof goal

If your proof goal is an implication `A → B`, with `intro h` you can assume `h : A`,
and then you must prove `B`.

## Implication as assumption

To use an implication among your assumptions, use the tactic `apply`.
-/
DefinitionDoc Arrow as "→" in "Logic"

/--
`A ↔ B` means that statements `A` and `B` are logically equivalent (“if and only if”).

## `↔` as proof target

To show `A ↔ B`, you can, for example, call `constructor`
and then prove `A → B` and `B → A` separately.

## `↔` as an assumption

You can break down an assumption of the form `h : A ↔ B` using `obtain ⟨h₁, h₂⟩ := h` into its two components
`h₁ : A → B` and `h₂ : B → A`.
However, you can also refer directly to these components with `h.mp` and `h.mpr`.
(The abbreviation `mp` stands for “modus ponens”.)
-/
DefinitionDoc Iff as "↔" in "Logic"

/--
Existential quantifier: If `P : A → Prop` is a predicate, then
`∃ a : A, P a` is the statement that an element `a` in `A` (more precisely: of type `A`)
exists for which the statement `P a` is true.
A pure existence statement ("there is an element of type `A`)
can be formulated, for example, as `∃ a : A, true` or as `Nonempty A`.

## `∃` as a proof goal

To prove a statement of the form `∃ a : A, …`,
you construct a suitable element `a` and then use the `use` tactic (`use a`).

## `∃` as an assumption

You can decompose an assumption of the form `h : ∃ a : A, P a` into its components using
`choose a ha using h` or `obtain ⟨a, ha⟩ := h` into `a : A` and `ha : P a`.
-/
DefinitionDoc Exists as "∃" in "Logic"

/--
Existential quantifier: If `P : A → Prop` is a predicate, then
`∃! a : A, P a` is the statement that *exactly one* element `a` in `A` (more precisely: of type `A`)
exists for which the statement `P a` is true.
The statement therefore has two parts: first, such an `a` exists, and second, `a` is unique.
## `∃!` as a proof goal

To prove a statement of the form `∃! a : A, …`, first construct a suitable element `a` and
then use the `use` tactic (`use a`), usually immediately followed by `simp`.
The proof goal should then have the following form:

`P a ∧ ∀ a' : A, P a' → a' = a`

On the left is `P a`: you still have to show that `a` has the required property.
On the right is the uniqueness statement: every element with this property is equal to `a`.

## `∃!` as an assumption

You can prove an assumption of the form `h : ∃! a : A, P a` with

```
  obtain ⟨a, h_exists, h_unique⟩ := h
  simp at h_unique
```
into its components
```
   a : A
   h_exists : P a
   h_unique : ∀ (y : A), P y → y = a
```
.
-/
DefinitionDoc ExistsUnique as "∃!" in "Logic"


/--
Universal quantifier: If `P : A → Prop` is a predicate, then
`∀ a : A, P a` is the statement that the statement `P a` is true for all `a` in `A`
(more precisely: for all `a` of type `A`).
## `∀` as a proof goal
To prove a statement of the form `∀ a : A, …`, first use `intro a` to select any element `a`.
## `∀` as an assumption
If `h : ∀ a : A, P a` is an assumption and `a₀ : A` is a concrete element, then `h a₀` is a notation for `P a₀`.

You can also use `specialize h a₀` to restrict the given assumption
over all possible `a` to an assumption `h : P a₀` over this concrete `a₀`.-/
DefinitionDoc Forall as "∀" in "Logic"


/--
The statement `True : Prop` is always true.

## `True` as a proof target

The tactics `tauto` and `decide` conclude every proof with `True` as the proof target.

## `True` as an assumption

As an assumption, `True` is not helpful at all.
-/
DefinitionDoc True as "True" in "Logic"

/--
The statement `False : Prop` is always false.

## `False` as proof target

If `False` is your proof target, you can try to find a contradiction in your assumptions, for example.
Once the contradiction is sufficiently evident, `contradiction` concludes such a proof.

If `False` is your proof goal and you have an assumption or lemma of the form `h : ¬ A` available,
you can use `apply h` to change the proof goal to `A`
(because `¬ A` means `A → False`).

## `False`  as an assumption

If you have `False` as an assumption, you can immediately end the proof with `contradiction`
– because, as is well known, any other statement follows from a false statement.
-/
DefinitionDoc False as "False" in "Logic"

/--
`¬ A` is the logical negation of `A`.
It is implemented internally as `A → False`.

Useful tactics are: `push_neg`, `by_contra`, `contrapose`.
You can also apply an assumption of the form `h : ¬ A` using `apply` to the proof target `False`.
-/
DefinitionDoc Not as "¬" in "Logic"

/--
Useful tactics for equality are: `rfl`, `rw`, `trans`
-/
DefinitionDoc Eq as "=" in "Logic"

/--
Inequality `x ≠ y` is defined as `¬ x = y`.  You can see this with `unfold Ne`.
-/
DefinitionDoc Ne as "≠" in "Logic"


/- NATÜRLICHE ZAHLEN -/

/--
`Even n` is the statement that `n : ℕ` is even:
```
∃ r : ℕ, n = r + r
```
You can easily check this with `unfold Even`.
-/
DefinitionDoc Even as "Even"

/--
`Odd n` is the statement that `n : ℕ` is odd:
```
∃ k : ℕ, n = 2 * k + 1
```
You can easily check this with `unfold Odd`.
-/
DefinitionDoc Odd as "Odd"

/--
For `n : ℕ`, `Prime n` means that `n` is a prime number.
To work with this definition, it is often helpful to rewrite it using the lemma
`prime_def`.
-/
DefinitionDoc Nat.Prime as "Prime"

/--
`succ : ℕ → ℕ` is the mapping `n ↦ n + 1`.
It therefore maps a natural number to its successor.
-/
DefinitionDoc Nat.succ as "succ"

/--
If `n : ℤ` is an integer greater than or equal to 0, then `n.toNat : ℕ` is the same number, interpreted as a natural number.
(If `n : ℤ` is a negative integer, then `n.toNat : ℕ` is also defined, but its value has no mathematical meaning.)

## Friends and relatives

A natural number `n : ℕ` can always be interpreted as an integer.
To do this, you either write it explicitly as `(n : ℤ)` or as `↑n`.
-/
DefinitionDoc toNat as "toNat"

/- MISCHMASCH -/

/--
For `x : ℝ`, `|x|` is the absolute value of `x`.
(Here, `|` is the usual vertical bar on the keyboard.)
-/
DefinitionDoc absValue as "|·|"

-- /-- `abs : ℝ → ℝ` ist die Betragsfunktion: `abs = fun x : ℝ ↦ |x|`
-- -/
-- DefinitionDoc absFunction as "abs"
--
-- This is literally true:
-- example : ((abs : ℝ → ℝ) = fun x : ℝ ↦ |x|) := by
--   rfl

/--
For a finite index set `I : Finset T`, `∑ i ∈ I, f i` is Leanic notation for the sum
$\sum_{i\in I} f(i)$.  You write the summation sign as `\sum`.
-/
DefinitionDoc Sum as "∑"

/--
For a finite index set `I : Finset T`, `∏ i ∈ I, f i` is the Leanic notation for the product
$\prod_{i\in I} f(i)$.  You write the product symbol as `\prod`.
-/
DefinitionDoc Prod as "∏"


/--
`P : MvPolynomial (Fin n) R` means that `P` is a polynomial in `n` indeterminates
`X 0`, …, `X (n-1)` with coefficients in `R`.
-/
DefinitionDoc MvPolynomial as "MvPolynomial"

/--
For a matrix `A`, `trace A` is the trace of `A`. The expression is also equivalent to `∑ i, A i i` in Leanic.
-/
DefinitionDoc Matrix.trace as "trace" in "Matrix"
