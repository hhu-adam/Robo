import GameServer.Commands

/--
With `apply`, you apply an implication `hAB : A → B`:

| before | tactic           | after |
|:------------ |:---------------- |:-------- |
| `⊢ B`        | `apply hAB`      | `⊢ A`    |
| `h : A `     | `apply hAB at h` | `h : B`  |

In both cases, the implication `hAB` can either be
given as an assumption or be an already known lemma.
-/
TacticDoc apply

/--
The `assumption` tactic closes the proof if one of the assumptions corresponds exactly to the proof target.
-/
TacticDoc assumption

/--
The tactic `by_cases h : P` begins a case distinction as to whether `P` is true or false.
For example, `by cases h : a = b` distinguishes between the cases `a = b` and `a ≠ b`.

The proof goal is duplicated for this purpose, and
the assumption `(h : P)` is added to the first “copy,”
while the assumption `(h : ¬P)` is added to the second “copy.”
-/
TacticDoc by_cases

/--
The tactic `by_contra h` initiates a proof by contradiction.
If `P` is your current proof goal, `by_contra h` generates a new assumption `(h : ¬ P)`
and sets the proof goal to `False`.

## Friends and relatives

* At the end of a proof by contradiction, there is usually `contradiction`:
this tactic closes the proof when it finds two obviously contradictory assumptions.
* If the proof goal is of the form `A → B`, you can use `contrapose`
to start a proof by contraposition.
-/
TacticDoc by_contra


/-
`change t` ändert das Beweisziel zu `t`. Voraussetzung ist, dass `t` und das alte Beweisziel
definitionsgleich sind.
Dies ist insbesonder hilfreich, wenn eine Taktik nicht merkt,
dass das Beweisziel definitionsgleich  ist zu einem
Term, der eigentlich gebraucht würde.

## Beispiel

Aktuelle Beweislage:
```
b: ℝ
⊢ 1 • b = b
```
wobei die Skalarmultiplikation als `fun (a : ℚ) (r : ℝ) => ↑a * r` definiert war.
Hier kannst du mit `change (1 : ℚ) * b = b` das Beweisziel umschreiben und anschließend mit Lemmas
über die Multiplikation beweisen.
-
TacticDoc change
-/

/--
An assumption of the form
```
h : ∃ (b : B), P b
```
can be decomposed, using `choose b hb using h`, into the components `b : B` and `hb : P b`.

More generally, you can use `choose` to select elements using the choice axiom:
from an assumption of the form
```
h : ∀ (a : A), ∃ (b : B), P a b
```
extracts `choose f hf using h`
a mapping `f : A → B` and the assumption `hf : ∀ (a : A), P a (f a)`.

(Here, `P : A → (B → Prop)` is a predicate that depends on two variables `a` and `b`.)
-/
TacticDoc choose


/--
The `constructor` tactic breaks down a proof goal into its constituent parts:

| before | after                |
|:------------ |:----------------------- |
| `⊢ A ∧ B`    | `⊢ A` and `⊢ B`         |
| `⊢ A ↔ B`    | `⊢ A → B` and `⊢ B → A` |

## Friends and relatives

* You can break down an *assumption* into its components using `obtain`.
* If you want to prove `A ∨ B`, you have to choose one side using `left` or `right`.
-/
TacticDoc constructor

/--
The tactic `contradiction` concludes the proof if it finds a contradiction in the assumptions.
Such a contradiction can look like this, for example:

* `h : n ≠ n`
* `h : A` and `h' : ¬A`
* `h : False`

## Friends and relatives

Normally, `contradiction` is used to conclude a proof by contradiction
that was opened with `by_contra`.
-/
TacticDoc contradiction

/--
The tactic `contrapose` changes a proof goal of the form `A → B` to `¬B → ¬A`, thereby
initiating a proof by contraposition.

## Friends and relatives

The tactic `revert h` can be useful for writing an assumption as an implication premise
before you use `contrapose`.
-/
TacticDoc contrapose

/-
Die Taktik `exact h` schließt das Beweisziel, wenn der Term `h` mit dem Beweisziel übereinstimmt.
-
TacticDoc exact
-/

/--
Two subsets of a given set are equal if they have the same elements.
If the proof goal is
```
A = B
```
for two subsets of `T` (i.e., for `A B : Set T`),
then `ext x` converts the proof goal into the equivalence
```
x ∈ A ↔ x ∈ B
```
-/
TacticDoc ext

/-
`fin_cases i` führt eine Fallunterscheidung, wenn `i` ein endlicher Typ ist.

## Details
`fin_cases i` ist insbesondere nützlich für `(i : Fin n)`, zum Beispiel als Index in
endlich dimensionalen Vektorräumen.

In diesem Fall bewirkt `fin_cases i`, dass du komponentenweise arbeitest.
-
TacticDoc fin_cases
-/

/--
Two mappings with the same range and domain are equal if
they take the same values on all elements of the domain.
A proof goal of the form
```
f = g
```
for mappings `f g : X → Y` is converted by `funext x`
into the equation
```
f x = g x
```.
-/
TacticDoc funext

/--
With `generalize`, you can generalize a proof goal
in the hope that a higher level of abstraction will allow for a simpler proof.
More precisely, `generalize h : a = b` replaces all occurrences of `a` in the proof goal with `b`
(and adds the assumption `h : a = b`).

## Example

A goal of the form
```
Even x ∨ ¬Even x
```
can be converted with
```
generalize h : (Even x) = A
```
into
```
A ∨ ¬A
```
(and then simply proven with `tauto`).
-/
TacticDoc generalize

/--
With `have h : P`, you introduce an intermediate result.
You must then prove this intermediate result
before you can continue with the actual proof.

## Friends and relatives
`suffices h : P` works in exactly the same way, except that you can continue with the main proof first and
only have to prove your intermediate result at the very end.
-/
TacticDoc «have»
/-
 `let h : Prop := A ∧ B` ist verwandt mit `have`, mit dem Unterschied, dass man mit `let`
  eine temporäre Definition einführt.
-/

/--
With `if … then … else`, you can define mappings with two branches of definition.

For example, `fun x ↦ if 0 ≤ x then x else -x` defines the absolute value function.

## Friends and relatives

* If you have `h : A` as an assumption, you can use
`rw [if_pos h]` to reduce the expression `if A then B else C` to `B`.
* If you have `h : ¬ A` as an assumption, you can use
`rw [if_neg h]` to reduce the expression `if A then B else C` to `C`.
-/
TacticDoc «if»

/--
The tactic `induction n` performs an inductive proof over `n`.
With `induction n with d dh`, you can specify names for the induction variable (here: `d`)
and the induction assumption (here: `hd`).
The tactic thus replaces the original proof goal with two new proof goals:
* an induction start, in which `n = 0` is set, and
* an induction step, in which the induction assumption `hd` is available to you.

## Modifications in this game

Outside of this game, `induction` is called `induction'`,
`0` is initially written as `Nat.zero` and `d + 1` as `Nat.succ d`.
These terms are identical in definition, but occasionally need to be explicitly rewritten with
`zero_eq` and `Nat.succ_eq_add_one`.
-/
TacticDoc induction
/- richtige `induction`-Syntax:
```
induction n with
| zero =>
  sorry
| succ m m_ih =>
  sorry
```
Da diese sich über mehrere Zeilen erstreckt, wird sie im Spiel nicht eingeführt.

Hifreiche Resultate

* `Nat.succ_eq_add_one`: schreibt `n.succ = n + 1` um.
* `Nat.zero_eq`: schreibt `Nat.zero = 0` um.

Beide sind definitionsgleich, aber manche Taktiken können nicht damit umgehen

* `obtain ⟨⟩ := n` ist sehr ähnlich zu `induction n`. Der Unterschied ist, dass bei
`obtain` keine Induktionshypothese im Fall `n + 1` zur Verfügung steht.
-/


/--
The tactic `intro` is used for   proof goals of the form `A → B` or `∀ x, P x`.

If your proof goal is `A → B`, `intro h` gives you the assumption `h : A`, and you then have to prove `B`.
If your proof goal is `∀ x, P x`, `intro x` gices you an arbitrary `x` and you have to prove `P x`.

| before | tactic       | after                     |
|:------------ |:------------ |:---------------------------- |
| `⊢ A → B`    | `intro h`    | `h : A`, `⊢ B`               |
| `⊢  x, P x`  | `intro x hx` | `x : X`, `hx : P x`, `⊢ P x` |


## Friends and relatives

The tactic `revert h` does the exact opposite of `intro h`.
-/
TacticDoc intro

/--
If the proof target is of the form `A ∨ B`, you choose `left` to show the left side.

## Friends and relatives

With `right`, you choose the right side accordingly.
-/
TacticDoc left

/--
The `let` tactic introduces a temporary definition, for example
`let x : ℕ := 5 ^ 2`.

Once `let x := …` defines a `x`, you can use the definition later with `simp only [x]`.
-/
TacticDoc «let»
-- * `have x : ℕ := 5 ^ 2` führt ebenfalls eine neue natürliche Zahle `x` ein, aber
--  Lean vergisst sofort, wie die Zahl definiert war. D.h. `x = 25` wäre dann nicht
--  beweisbar. Mit `let x : ℕ := 5 ^ 2` ist `x = 25` durch `rfl` beweisbar.
--
-- * `set x : ℕ := 5 ^ 2` macht das Gleiche wie `let`, aber versucht auch `x` im Beweisziel überall einzusetzen wo `5 ^ 2` steht.
-- we decided not to introduce `set`

/-
`set f := _` funktioniert wie `let` aber versucht auch `f` im Beweisziel überall einzusetzen.
-
TacticDoc set
-/

/--
The tactic `linarith` can show that a linear equation or inequality follows from given equations or inequalities.
It is quite flexible and works just as well in ℕ as in ℝ.
However, the (in)equations must be given individually, not logically linked.
An assumption of the form
```
h : m ≤ x → n < x
```
must first be rewritten with
```
rw [imp_iff_or_not] at h
```
to
```
h : n < x ∨ ¬m ≤ x
```
so that `linarith` can do something with it.
-/
TacticDoc linarith

/--
The tactic `omega` can show that a linear equation or inequality in `ℕ` or `ℤ`
follows from given equations or inequalities.
Unlike `linarith`, it can also handle logical connections between (in)equations.
-/
TacticDoc omega

-- Dafür kann  `linarith` z.B. für `x y a b : ℕ` wie `ring` zeigen: `x * a + y * a = (x + y) * a` zeigen,
-- siehe Prado level 2; `omega` kann das nicht.

/--
The tactic `push Not` or `push ¬ _ ` (`push`, `Not`, `¬ _`)  pushes negation past quantifiers:

| before       | after      |
|:------------ |:-------------|
| `¬∀ x, P x`  | `∃ x, ¬P x`  |
| `¬∃ x, P x`  | `∀ x, ¬P x`  |

In nested expressions, it pushes the negation `¬` as far to the right as possible.
For example, the proof goal
```
  ¬ ∀ ε, ∃ δ, ∀ y, | x - y | < δ → | f x - f y | < ε
```
with `push Not`
```
  ∃ ε, ∀ δ, ∃ y, ¬ (| x - y | < δ → | f x - f y | < ε)
```

## Friends and relatives

The two lemmas `not_forall` and `not_exists` can be applied individually with `rw`.
-/
TacticDoc push

/--
The `obtain` tactic breaks down an assumption into its individual parts.

| before       | tactic                 | after                                   |
|:------------------ |:--------------------- - |:------------------------------------------ |
| `h : A ∧ B`        | `obtain ⟨h₁, h₂⟩ := h` | `h₁ : A` and `h₂ : B`                      |
| `h : A ↔ B`        | `obtain ⟨h₁, h₂⟩ := h` | `h₁ : A → B` and `h₂ : B → A`              |
| `h : Nonempty X`   | `obtain ⟨x⟩ := h`      | `x : X`                                    |
| `h : ∃ x : X, P x` | `obtain ⟨x, hx⟩ := h`  | `x : X` and `hx : P x`                     |
| `h : A ∨ B`        | `obtain h \| h := h`   | a target with `h : A`, a target with `h : B` |

Type the brackets in the first four examples as `\<` or `\>`.
Here, `⟨_, _⟩` is the *anonymous constructor*.
You can think of it as similar to the tuple notation in
“an abelian group is a tuple $(G, 0, +)$ such that ...”.
-/
TacticDoc obtain
--
-- * Die Wildcard `obtain ⟨⟩ := h` entscheidet selbständig, welcher Fall vorliegt und
--   benennt die entehenden Annahmen.
--
-- * Für `n : ℕ` hat `obtain ⟨⟩ := n` einen ähnlichen Effekt wie `induction n` mit dem Unterschied,
--   dass im Fall `n + 1` keine Induktionshypothese zur Verfügung steht.

/-
`refine' { .. }` wird benötigt um eine Struktur (z.B. ein $R$-Modul) im Taktikmodus in einzelne
Beweisziels aufzuteilen. Danach hat man ein Beweisziel pro Strukturfeld.

(*Bemerkung*: Es gibt in Lean verschiedenste bessere Varianten dies zu erreichen,
z.B. \"Term Modus\" oder \"anonyme Konstruktoren\", aber für den Zweck des Spieles bleiben wir
bei dieser Syntax.)
-
TacticDoc refine'
-/

/--
The tactic `revert h` adds the assumption `h` as an implication premise to the proof goal:
from `h : A` and `⊢ B`, we get `⊢ A → B`.

## Friends and relatives

The tactic `intro h` does the exact opposite of `revert h`.
-/
TacticDoc revert


/--
The tactic `rfl` proves `X = X`.  More precisely, `rfl` closes every proof target of the form `A = B`,
where `A` and `B` are identical in definition.
-/
TacticDoc rfl
-- rfl beweist auch 1 + 1 = 2 in ℕ, denn intern sind beide Seiten `0.succ.succ`.

/--
If the proof target is of the form `A ∨ B`, you choose `right` to show the right side.

## Friends and relatives

With `left`, you choose the left side accordingly.
-/
TacticDoc right

/--
The `ring` tactic proves equations with the operations `+, -, *, ^` in semirings,
in particular in ℕ, ℤ, ℚ, ℝ, …   It works particularly well in commutative rings.
-/
TacticDoc ring
-- `ring` braucht Typen `R` mit Instanzen `Ring R` oder `Semiring R`.
-- Die Taktik ist besonders auf kommutative Ringe (`CommRing R`) ausgelegt.

/--
If you have given an equation `h : X = Y` or an equivalence `h : X ↔ Y` as an assumption or lemma,
you can use `rw [h]` to replace all occurrences of `X` in the proof target with `Y`.

## Variants

* `rw [←h]` applies `h` backwards, i.e., replaces all `Y` with `X`.
* `rw [h, g, ←f]` applies `h`, `g`, and (backwards) `f`.
* `rw [h] at h₂` performs the replacements in the assumption `h₂`, not in the proof target
* `nth_rw`: If `h` has arguments, e.g., `n` in
```
   h : ∀ n, 2*n = f n
   ```
   or in
```
   h (n : ℕ) : 2*n = f n
   ```
   `rw [h]` searches the proof target from left to right for a matching expression,
   and then replaces *all* occurrences of *the first* expression that the tactic finds.
   With `nth_rw k [h]`, you can replace all occurrences of the `k`th expression instead.

  | before    | tactic       | after        |
  |:----------------- |:------------- - |:----------------- |
  | `2*a + 2*b > 2*a` | `rw [h]`       | `f a + 2*b > f a` |
  |                   | `nth_rw 2 [h]` | `2*a + f b > 2*a` |
-/
TacticDoc rw

/--
The `simp` tactic attempts to apply a large number of lemmas to simplify a given expression.
(Technically, these are all lemmas in `mathlib` that are marked with `@[simp]`.)

## Variants

* `simp [h]` additionally uses the assumption `h` or the lemma `h` for simplification
* `simp [F]` additionally uses the definition of `F`
* `simp only [h,f,g]` exclusively uses the assumptions/lemmas/definitions `h`, `f`, and `g`
* `simp?` shows you which lemmas were used
-/
TacticDoc simp

/-
`simp_rw [h₁, h₂, h₃]` versucht wie `rw` jedes Lemma der Reihe nach zu Umschreiben zu verwenden,
verwendet aber jedes Lemma so oft es kann.

## Details

Es bestehen aber drei grosse Unterschiede zu `rw`:

* `simp_rw` wendet jedes Lemma so oft an wie es nur kann.
* `simp_rw` kann besser unter Quantoren umschreiben als `rw`.
* `simp_rw` führt nach jedem Schritt ein `simp only []` aus und vereinfacht dadurch grundlegendste
  Sachen.
-
TacticDoc simp_rw
-/

/--
`specialize h a₁ a₂` is equivalent to `have h := h a₁ a₂`: the tactic replaces an assumption
`h : ∀ m₁ m₂, P m₁ m₂` with the special case `h : P a₁ a₂`.

If you want to specialize multiple times, instead of `specialize` you should use `have`,
since `specialize h …` overwrites the old assumption `h`.
From the above assumption `h`, you can obtain the following three assumptions with
```
have ha := h a₁ a₂
have hb := h b₁ b₂
```
:
```
h : ∀ m₁ m₂, P m₁ m₂
ha : P a₁ a₂
hb : P b₁ b₂
```
-/
TacticDoc specialize


/--
With `suffices h : P`, you introduce a proof section in which you show
that the desired proof goal follows from `P`.
Then you prove `P`.

## Friends and relatives
`have h : P` works the same way, except that you must first prove `P` before you can
continue with the main proof.
-/
TacticDoc «suffices»


/--
With `symm` (for “symmetry”), you swap the sides of an equation (`=`) or equivalence (`↔`) in the proof target.

## Variants
* `symm at h` operates on the assumption `h` instead of the proof target
* `h.symm` is the result of `symm at h` and can be used like `h`

Each of the following three tactics or tactic sequences therefore has the same effect:
* `rw [←h]`
* ```
  symm at h
  rw [h]
  ```
* `rw [h.symm]`
-/
TacticDoc symm

/--
With `trans`, you insert an intermediate step into an equation or equivalence.

| before | tactic    | after                |
|:------------ |:--------- |:----------------------- |
| `⊢ A = C`    | `trans B` | `⊢ A = B` and `⊢ B = C` |
| `⊢ A ↔ C`    | `trans B` | `⊢ A ↔ B` and `⊢ B ↔ C` |

Since you can repeat the tactic several times, it is suitable for
performing a “calculation” `A = B₁ = B₂ = B₃ … = C` step by step.

(Outside of the game, however, the multi-line tactic `calc` is better suited for such calculations.)
-/
TacticDoc trans

/--
With `decide`, you can prove statements that can be decided using a simple algorithm.
These include, in particular, `True` and statements about concrete numbers such as:
- `Even 4`
- `2 ≤ 5`
- `4 ≠ 6`
- `Prime 7`
-/
TacticDoc decide
-- Konkret sucht `decide` für eine Aussage `P`  nach einer Instanz `Decidable P`
-- welche dann evaluiert entweder wahr oder falsch rausgibt.

/--
With `unfold F`, you can write out the definition `F` in the proof goal.
With `unfold F at h`, you do the same thing, but in the assumption `h`.

Although the proof goal or assumption before and after `unfold` are identical in definition,
many tactics (e.g., `push Not` or `rw`) operate on a syntactic level;
they do not “see through definitions.”

## Friends and Relatives

The tactics `unfold F` and `simp only [F]` do practically the same thing.
-/
TacticDoc unfold
-- * `change _` ist eine andere Taktik (nicht im Spiel), die das aktuelle Beweisziel in einen definitionsgleichen Ausdruck
--  umschreibt. Diese Taktik braucht man auch manchmal um zu hacken, wenn Lean Mühe hat, etwas zu verstehen.

/--
If the proof target is of the form `∃x, P x`, you can use `use x` to specify a concrete element
for which you want to prove `P x`.
-/
TacticDoc use

/--
The tactic `tauto` proves logical tautologies.

# Friends and relatives

Sometimes the proof target must first be abstracted with `generalize` so that `tauto` recognizes the tautology.
-/
TacticDoc tauto
