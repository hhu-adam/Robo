import GameServer.Commands

/-! ## Definitions -/


/- ABBILDUNGEN -/

/--
Eine Abbildung `f` is injektiv, wenn gilt:

```
∀ a b, f a = f b → a = b
```
-/
DefinitionDoc Function.Injective as "Injective"


/--
Eine Abbildung `f` is surjektiv, wenn gilt:

```
∀ b, ∃ a, f a = b
```
-/
DefinitionDoc Function.Surjective as "Surjective"


/--
Eine Abbildung ist bijektiv, wenn sie injektiv und surjektiv ist.
-/
DefinitionDoc Function.Bijective as "Bijective"


/--
Eine Abbildung `f` ist strikt monoton, wenn gilt:

```
∀ a b, a < b → f a < f b
```
-/
DefinitionDoc StrictMono as "StrictMono"


/-- `Function.RightInverse f g` ist als `LeftInverse g f` definiert.
Das bedeutet im Klartext natürlich `∀ x, g (f x) = x`.

Du musst leider `Function.RightInverse`  statt `RightInverse` schreiben,
da `RightInverse` Leansch mehrdeutig ist.
-/
DefinitionDoc Function.RightInverse as "RightInverse"
-- Note the fact that one sees `LeftInverse` but `Function.RightInverse` is because
-- some mathlib init-file defines `_root_.RightInverse`. mathlib4#11415 investigates this.


/--
`LeftInverse g f` bedutet `g ∘ f = id`, oder genauer: `∀ x, g (f x) = x`, wie du mit `unfold` leicht siehst.
-/
DefinitionDoc Function.LeftInverse as "LeftInverse"


/--
`HasRightInverse f` bedeutet, dass `f` ein Rechtsinverses besitzt.

`HasLeftInverse f` bedeutet, dass `f` ein Linkssinverses besitzt.
-/
DefinitionDoc Function.HasRightInverse as "Has…Inverse"


/--
Für eine Selbstabbildung `f : A → A` und ein Element `a : A` ist `IsFixedPt f a` die Aussage `f a = a`.
Du kannst die Definition mit `unfold IsFixedPt` leicht ausschreiben.
-/
DefinitionDoc Function.IsFixedPt as "IsFixedPt"

/--
Für eine Abbildung `f : A → A` ist `fixedPoints f : Set A` die Menge der Fixpunkte von `f `.
Du kannst die Definition mit `unfold fixedPoints` leicht ausschreiben.
-/
DefinitionDoc Function.fixedPoints as "fixedPoints"

/--
Für zwei Teilmengen `A` und `B` von `S` (also `A B : Set S`) ist `A ∪ B` ihre die Vereinigung.
Du schreibst `∪` als `\\union`.
-/
DefinitionDoc Set.union as "∪"

/--
Für zwei Teilmengen `A` und `B` von `S` (also `A B : Set S`) ist `A ∩ B` ihr Schnitt.
Du schreibst `∪` als `\\inter`.
-/
DefinitionDoc Set.inter as "∩"

/--
Für eine Abbildung `f : A → B` ist `range f` die gesamte Bildmenge von `f`:
```
range f = {f a | a : A}
        = {  b | ∃ a, f a = b}
```
Das ist also im wesentlichen eine andere Schreibweise für `f '' univ`.
Um damit zu arbeiten, ist `mem_range` ganz nützlich:
```
x ∈ range f ↔ ∃ a, f a = b
```
-/
DefinitionDoc Set.range as "range"

/--
Für eine Abbildung `f : A → B` ist `image f : Set A → Set B`
eine der induzierten Abbildung auf den Potenzmengen –
sie bildet eine Teilmenge von `A` ab auf das Bild `f '' A` dieser Teilmenge unter `f`.
-/
DefinitionDoc Set.image as "image"

/--
Für eine Abbildung `f : A → B` ist `preimage f : Set B → Set A`
eine der induzierten Abbildung auf den Potenzmengen –
sie bildet eine Teilmenge von `B` ab auf das Urbild `f ⁻¹' A` dieser Teilmenge unter `f`.
-/
DefinitionDoc Set.preimage as "preimage"


/--
Für eine Abbildung `f : A → B` und eine Teilmenge `S` von `A` ist
```
f '' S = {f a | a ∈ S}
       = {b | ∃ a ∈ S, f a = b}
```
ihr Bild unter `f`.  Beachte das Leerzeichen zwischen `f` und `''`.
-/
DefinitionDoc Set.fimage as "f ''"

/--
Für eine Abbildung `f : A → B` und eine Teilmenge `T` von `B` ist
```
f ⁻¹' T = { a | f a ∈ T}
```
ihr Urbild unter `f`.
Du schreibst das als `f \-1'`.
Beachte das Leerzeichen zwischen `f` und `\-1'`.
-/
DefinitionDoc Set.fpreimage as "f ⁻¹'"

/--
Die Notation `fun x ↦ _` wird verwendet, um „anonyme Funktionen“ zu definieren.
Zum Beispiel definiert `fun (x : ℤ) ↦  -x` die Negation `ℤ → ℤ`, ohne ihr einen Namen zu geben.
Den Pfeil `↦` schreibst du als `\maps` oder `\mapsto`.
Alternativ kannst du statt `↦` auch `=>` verwenden.
-/
DefinitionDoc Symbol.function as "fun x ↦ _"


/- MENGEN -/

/-- `A : Set T` bedeutet, dass `A` eine Teilmenge von `T` ist
(oder genauer, dass `A` eine Menge ist, die aus Elementen vom Typ `T` besteht).
-/
DefinitionDoc Set as "Set"

/-- Für eine Teilmenge `A : Set T` und ein Element `a` aus `T` (genauer: vom Typ `T`) bedeutet `a ∈ A`, dass
`a` in `A` liegt.

Für Teilmengen der Form `A = { a : T | P a }` kannst du die Aussage
`a ∈ A` mit `simp` zu `P a` vereinfachen.
-/
DefinitionDoc Mem as "∈"

/-- Für ein Prädikat `P : T → Prop` ist `{ a : T | P a } : Set P` die Teilmenge,
die aus all jenen Elementen besteht, die das Prädikat erfüllen.  Zum Beispiel ist
```
{ n : ℕ | Even n }
```
die Menge der geraden natürlichen Zahlen.

Die Aussage `a ∈ { a : T | P a }` kannst du mit `simp` zu `P a` vereinfachen.
-/
DefinitionDoc setOf as "{·|·}"

/-- Für zwei Teilmengen `(A B : Set T)` ist `A\B` die Differenz aus `A` and `B`,
bestehend aus allen Elementen von `A`, die nicht in `B` liegen.-/
DefinitionDoc SDiff as "·\\·"

/--
Für `A B : Set T` bedeutet `A ⊆ B`, dass `A` in `B` enthalten ist.

Mit `rw [subset_iff]` kannst du `A ⊆ B` zu `∀ x, x ∈ A → x ∈ B` umschreiben.

Ist `A ⊆ B` das Beweisziel, kannst du auch direkt mit `intro a ha`
ein Element `a` mit `ha : a ∈ A` wählen (und dann `a ∈ B` zeigen).

Ist `h : A ⊆ B` eine Annahme, erhältst du mit `obtain ⟨a, ha⟩ := h` ein Element `a` mit `ha : a ∈ A`.

Du schreibst `⊆` als `\subset`.
-/
DefinitionDoc Subset as "⊆"

/-- `∅ : Set T` ist die leere Teilmenge.
Im Formaloversum ist also `∅ : Set ℕ` etwas anderes als `∅ : Set ℝ`
– das eine ist eine Teilmenge von ℕ, das andere eine Teilmenge von ℝ!

Mit `rw [eq_empty_iff_forall_not_mem]` überführst du eine Gleichung der Form `S = ∅` in die
Aussage `∀ (x : T), x ∉ s`.

Du schreibst `∅` als `\\emptyset`.
-/
DefinitionDoc Set.empty as "∅"

/-- `univ : Set T` ist die “Teil”menge, die aus *allen* Elementen vom Typ `T` besteht.

Mit `rw [eq_univ_iff_forall]` überführst du eine Gleichung der Form `S = univ` in die
Aussage `∀ (x : T), x ∈ S`.
-/
DefinitionDoc Set.univ as "univ"

/-- Für eine endliche Teilmenge `A : Finset T` und ein Element `a : T` ist
`insert a A` eine andere Schreibweise für `A ∪ {a}`.
Sollte `a` bereits in `A` liegt, ist offenbar `insert a A = A`.
-/
DefinitionDoc Finset.insert as "insert"

/-- Für eine endliche Teilmenge `A : Finset T` und ein Element `a : T` ist
`erase A a` eine andere Schreibweise für `A \ {a}`.
Falls `a` gar nicht in `A` liegt, ist offenbar `erase A a = A`.
-/
DefinitionDoc Finset.erase as "erase"

/-- Für eine endliche Teilmenge `A : Finset T` ist `card A : ℕ` die Kardinalität von `A`,
also die Anzahl der Elemente in `A`.-/
DefinitionDoc Finset.card as "card"

/-- Für `n : ℕ` ist `Fin n` die Menge $\{0, \dots, n-1\}$.

(`Fin n` ist zu unterscheiden von `Icc 0 (n-1)`:
`Fin n` ist eine Menge, oder genauer ein Typ, also `Fin n : Type`,
während `Icc 0 (n-1) : Finset ℕ` eine endliche Teilmenge von `ℕ` ist.)
-/
DefinitionDoc Fin as "Fin"

-- DefinitionDoc Disjoint as "Disjoint"
-- "
-- "

/-- `Nonempty T` bedeutet, dass ein Element in `T` („vom Typ `T`“) existiert.
Ist `h : Nonempty T` als Annahme gegeben, erhalten wir ein Element `t : T` mit `obtain ⟨t⟩ := h`.
Haben wir umgekehrt bereits ein Element `t : T` gegeben oder konstruiert,
so können wir `Nonempty T` mit `use t` beweisen.

Analog ist für eine Teilmenge `A : Set T` die Aussage `Nonemty A` definiert als als `∃ x, x ∈ A`.
Das kannst du in diesem Fall leicht mit `unfold Nonempty` überprüfen.
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

-- LOGIK

/--
`A ∧ B` ("und") ist die Aussage, dass sowohl `A` als auch `B` wahr ist.

## `A ∧ B` als Beweisziel

Die Taktik `constructor` erlaubt dir, die beiden Teilaussagen `A` und `B` einzeln zu beweisen.

## `A ∧ B` als Annahme

Mit `obtain ⟨h₁, h₂⟩ := h` zerlegst du eine Annahme der Form `h : A ∧ B`
in ihre Bestandteile `h₁ : A` und `h₂ : B`.
-/
DefinitionDoc And as "∧"

/--
`A ∨ B` ("oder") ist die Aussage, dass mindestens eine der Aussagen `A`, `B` wahr ist.


-/
DefinitionDoc Or as "∨"


/--
Für `A B : Prop` ist `A → B` die Implikation „`A` impliziert `B`“.
Für andere `X Y : Type` ist `X → Y` eine Abbildung, die Werte aus `X` nach `Y` abbildet.

## Implikation als Beweisziel

Ist dein Beweisziel eine Implikation `A → B`, so kannst du mit `intro h` `h : A` annehmen,
und musst dann `B` beweisen.

## Implikation als Annahme

Um eine Implikation unter der Annahmen zu verwenden benutzt du die Taktik `apply`.
-/
DefinitionDoc Arrow as "→"


/-- Existenzieller Quantor: Ist `P : A → Prop` ein Prädikat, so ist
`∃ a : A, P a` die Aussage, dass ein Element `a` in `A` (genauer: vom Typ `A`)
existiert, für das die Aussage `P a` wahr ist.
Eine reine Existenzaussage („es gibt ein Element vom Typ `A`)
lässt sich zum Beispiel als `∃ a : A, true` oder als `Nonempty A` formulieren.

## `∃` als Beweisziel

Um eine Aussage der Form `∃ a : A, …` zu beweisen,
konstruierst du ein geeignetes Element `a` und nutzt dann die `use`-Taktik (`use a`).

## `∃` als Annahme

Eine Annahme der Form `h : ∃ a : A, P a` kannst du mit
`choose a ha using h` oder `obtain ⟨a, ha⟩ := h` in ihre Bestandteile `a : A` und `ha : P a`
zerlegen.
-/
DefinitionDoc Exists as "∃"

/-- Existenzieller Quantor: Ist `P : A → Prop` ein Prädikat, so ist
`∃! a : A, P a` die Aussage, dass *genau ein* Element `a` in `A` (genauer: vom Typ `A`)
existiert, für das die Aussage `P a` wahr ist.
Die Aussage hat also zwei Teile: erstens existiert
solch ein `a`, zweitens ist `a` eindeutig.

## `∃!` als Beweisziel

Um eine Aussage der Form `∃! a : A, …` zu beweisen, konstruierst du zunächst ein geeignetes Element `a` und
nutzt dann die `use`-Taktik (`use a`), in der Regel unmittelbar gefolgt von `simp`.
Danach sollte das Beweisziel folgende Form haben:

`P a ∧ ∀ a' : A, P a' → a' = a`

Links steht `P a`: du musst noch zeigen, dass `a` die geforderte Eigenschaft hat.
Rechts steht die Eindeutigkeitsaussage: jedes Element mit dieser Eigenschaft ist gleich `a`.

## `∃!` als Annahme

Eine Annahme der Form `h : ∃! a : A, P a` kannst du mit

```
  obtain ⟨a, h_exists, h_unique⟩ := h
  simp at h_unique
```
in die Bestandteile
```
   a : A
   h_exists : P a
   h_unique : ∀ (y : A), P y → y = a
```
zerlegen.
-/
DefinitionDoc ExistsUnique as "∃!"


/-- Universeller Quantor: Ist `P : A → Prop` ein Prädikat, so ist
`∀ a : A, P a` die Aussage, dass die Aussage `P a` für alle `a` in `A`
(genauer: für alle `a` vom Typ `A`) wahr sei.

Um eine Aussage der Form `∀ a : A, …` zu beweisen, wählt man mit `intro a` zunächst ein
beliebiges Element `a`.

Ist `h : ∀ a : A, P a` eine Annahme und `a₀ : A` ein konkretes Element, so ist `h a₀`
eine Notation für `P a₀`.  Man kann auch mit `specialize h a₀` die gegebene Annahme
über alle möglichen `a` zu einer Annahme `h : P a₀` über dieses konkrete `a₀` einschränken.
-/
DefinitionDoc Forall as "∀"

/--
Nützliche Taktiken für Gleicheit sind: `rfl`, `rw`, `trans`
-/
DefinitionDoc Eq as "="

/-- `Even n` ist die Aussage dass `n : ℕ` gerade ist. -/
DefinitionDoc Even as "Even"

/--
Die Aussage `False : Prop` ist nie wahr.

Lean benützt diese intern für Widersprüche, ein Widerspruch ist ein Beweis `(hF : False)` von
`False` und z.B. `¬ A` ist als `A → False` implementiert.
-/
DefinitionDoc False as "False"

/-- Genau-dann-wenn (if-and-only-if). Can meistens mit `constructor` oder `obtain ⟨fwd, bwd⟩ := h`
in Einzelteile zerlegt werden.

Bei einer Annahme `h : A ↔ B`, heissen die Einzelteile zudem `h.mp : A → B` und `h.mpr : B → A`.
-/
DefinitionDoc Iff as "↔"

/--
Ungleichheit `x ≠ y` ist definiert als `¬ x = y`.  Du siehst das mit `unfold Ne`.
-/
DefinitionDoc Ne as "≠"

/--
`Nonempty U` ist eine Instanz, die aussagt, dass `U` mindestens ein Element
enthält.

Wenn `h : Nonempty U`, dann kriegt man mit `obtain ⟨d⟩ := h` eine solches Element `d : U`.
-/
DefinitionDoc Nonempty as "Nonempty"

/--
`¬ A` ist intern als `A → False` implementiert.

Nütliche Tactiken sind: `push_neg`, `by_contra`, `contrapose`.
-/
DefinitionDoc Not as "¬"

/-- `Odd n` ist die Aussage dass `n : ℕ` ungerade ist. -/
DefinitionDoc Odd as "Odd"


/--
Für `n : ℕ` bedeutet `Prime n`, dass `n` eine Primzahl ist.
Um mit dieser Definition zu arbeiten, ist es oft hilfreich, sie mit dem Lemma
`prime_def` umzuschreiben.
-/
DefinitionDoc Nat.Prime as "Prime"

/--
`succ : ℕ → ℕ` ist die Abbildung `n ↦ n + 1`.
Sie bildet also eine natürliche Zahl auf ihren Nachfolger (englisch *successor*) ab.
-/
DefinitionDoc Nat.succ as "succ"

/-- `(A : Prop)` ist eine beliebige Aussage, ohne weitere Angabe, ob diese wahr, falsch oder
nicht beweisbar ist.

Siehe auch `(True : Prop)` und `(False : Prop)` die uneingeschränkt wahre (rsp. falsche)
Aussage.
-/
DefinitionDoc «Prop» as "Prop"

/-- Die Aussage `True : Prop` ist immer wahr. -/
DefinitionDoc True as "True"

/-- Die Aussage `False : Prop` ist immer falsch. -/
DefinitionDoc False as "False"


/-- Für eine endliche Indexmenge `I : Finset T` ist `∑ i ∈ I, f i` die leansche Schreibweise für die Summe
$\sum_{i\in I} f(i)$.  Du schreibst das Summenzeichen als `\sum`.
 -/
DefinitionDoc Sum as "∑"

/-- Für eine endliche Indexmenge `I : Finset T` ist `∏ i ∈ I, f i` die leansche Schreibweise für das Produkt
$\prod_{i\in I} f(i)$.  Du schreibst das Produktzeichen als `\prod`.
 -/
DefinitionDoc Prod as "∏"

/-- Für eine Teilmenge `A : Set T` bedeutet `Set.Finite A`, dass `A` nur endlich viele Element hat.
Ist `h : Set.Finite A` als Annahme gegeben, so ist `h.toFinset : Finset T` dieselbe Teilmenge `A`,
aber nun explizit als endliche Teilmenge aufgefasst.
-/
DefinitionDoc Set.Finite as "Set.Finite"


/-- Für `x : ℝ` ist `|x|` der Betrag von `x`.
(Hier ist `|` der gewöhnliche senkrechte Strich auf der Tastatur.)
-/
DefinitionDoc absValue as "|·|"

-- /-- `abs : ℝ → ℝ` ist die Betragsfunktion: `abs = fun x : ℝ ↦ |x|`
-- -/
-- DefinitionDoc absFunction as "abs"
--
-- This is literally true:
-- example : ((abs : ℝ → ℝ) = fun x : ℝ ↦ |x|) := by
--   rfl

/-- `P : MvPolynomial (Fin n) R` bedeutet, dass `P` ein Polynomial in `n` Unbestimmten
`X 0`, …, `X (n-1)` mit Koeffizienten in `R` ist. -/
DefinitionDoc MvPolynomial as "MvPolynomial"
