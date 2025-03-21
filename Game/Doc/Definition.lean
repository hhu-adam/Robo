import GameServer.Commands

/-! ## Definitions -/



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
DefinitionDoc Function.StrictMono as "StrictMono"


/-- `Function.RightInverse f g` ist als `LeftInverse g f` definiert.
Das bedeutet im Klartext natürlich `∀ x, g (f x) = x`.

Man muss leider `Function.RightInverse`  statt `RightInverse` schreiben,
da `RightInverse` allein in Leansch mehrdeutig ist.
-/
DefinitionDoc Function.RightInverse as "RightInverse"
-- Note the fact that one sees `LeftInverse` but `Function.RightInverse` is because
-- some Mathlib init-file defines `_root_.RightInverse`. mathlib4#11415 investigates this.


/--
`LeftInverse g f` bedutet `g ∘ f = id`, oder genauer: `∀ x, g (f x) = x`, wie man mit `unfold` leicht sieht.
-/
DefinitionDoc Function.LeftInverse as "LeftInverse"

/--
`HasRightInverse f` bedeutet, dass `f` ein Rechtsinverses besitzt.

`HasLeftInverse f` bedeutet, dass `f` ein Linkssinverses besitzt.
-/
DefinitionDoc Function.HasRightInverse as "Has…Inverse"

/--
Für zwei Teilmengen `A` und `B` von `S` (also `A B : Set S`) ist `A ∪ B` die Vereinigung der Teilmengen `A` und `B` von `S`.  Du schreibst `∪` als `\\union`.
-/
DefinitionDoc Set.union as "∪"

/--
Für zwei Teilmengen `A` und `B` von `S` (also `A B : Set S`) ist `A ∩ B` der Schnitt der Teilmengen `A` und `B` von `S`.  Du schreibst `∪` als `\\inter`.
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
einer der induzierten Abbildung auf den Potenzmengen –
sie bildet eine Teilmenge von `A` ab auf das Bild dieser Teilmenge unter `f`.
-/
DefinitionDoc Set.image as "image"

/--
Für eine Abbildung `f : A → B` ist `preimage f : Set B → Set A`
eine der induzierten Abbildung auf den Potenzmengen –
sie bildet eine Teilmenge von `B` ab auf das Urbild dieser Teilmenge unter `f`.
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
, und für eine Teilmenge `T` von `B` ist
```
f ⁻¹' T = { a | f a ∈ T}
```
ihr Urbild unter `f`.
Du schreibst das als `f \\-1'`.
Beachte das Leerzeichen zwischen `f` und `\\-1'`.
-/
DefinitionDoc Set.fpreimage as "f ⁻¹'"

/--
Anonyme Funktionen kann man mit `fun (x : ℤ)  2 * x` definieren und
wie andere Objekte verwenden.  Den Pfeil `↦` schreibt man als `\\maps` oder `\\mapsto`.
Alternativ kann man statt `↦` auch `=>` verwenden.
-/
DefinitionDoc Symbol.function as "fun x ↦ _"

-- DefinitionDoc Set.preimage as "preimage"
-- "
-- "


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

/-- Für zwei Teilmengen `(A B : Set T)` ist `A\\B` die Differenz aus `A` and `B`,
bestehend aus allen Elementen von `A`, die nicht in `B` liegen.-/
DefinitionDoc SDiff as "·\\·"

/--
Für `A B : Set T` bedeutet `A ⊆ B`, dass `A` in `B` enthalten ist.

Mit `rw [subset_iff]` kannst du `A ⊆ B` zu `∀ x, x ∈ A → x ∈ B` umschreiben.

Ist `A ⊆ B` das Beweisziel, kannst du auch auch direkt mit `intro a ha`
ein Element `a` mit `ha : a ∈ A` wählen (und dann `a ∈ B` zeigen).

Ist `h : A ⊆ B` eine Annahme, erhältst du mit `obtain ⟨a, ha⟩ := h` ein Element `a` mit `ha : a ∈ A`.

Um `⊆` zu schreiben, tippst du `\subset`.
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

/-- `univ : Set T` ist die “Teil”menge, die aus *allen* Elementen vom vom Typ `T` besteht.

Mit `rw [eq_univ_iff_forall]` überführst du eine Gleichung der Form `S = univ` in die
Aussage `∀ (x : T), x ∈ S`.
-/
DefinitionDoc Set.univ as "univ"

/-- Für eine endliche Teilmenge `A : Finset T` und ein Element `a : T` ist
`insert a A` eine andere Schreibweise für `A ∪ {a}`.
Es wird keine inhärente Annahme getroffen, ob `a` bereits in `A` liegt, oder nicht.
-/
DefinitionDoc Finset.insert as "insert"

/-- Für eine endliche Teilmenge `A : Finset T` und ein Element `a : T` ist
`erase A a` eine andere Schreibweise für `A \ {a}`.
-/
DefinitionDoc Finset.erase as "erase"

/-- Für eine endliche Teilmenge `A : Finset T` ist `card A : ℕ` die Kardinalität von `A`,
also die Anzahl der Elemente in `A`.-/
DefinitionDoc Finset.card as "card"

-- DefinitionDoc Disjoint as "Disjoint"
-- "
-- "

-- DefinitionDoc Set.Nonempty as "Nonempty" "

-- `A.Nonemty` ist als `∃ x, x ∈ A` definiert.
-- "


-- LOGIK

/--
`A ∧ B` ("und") ist die Aussage dass sowohl `A` als auch `B` wahr ist.
-/
DefinitionDoc And as "∧"

/--
* Für `A B : Prop` ist `A → B` eine Implikation "`A` impliziert `B`"
* Für andere `X Y : Type` ist `X → Y` eine Funktion, die Werte aus `X` nach `Y` abbildet,
  z.B. `f : ℕ → ℤ := n ↦ -n`.
-/
DefinitionDoc Arrow as "→"


/-- Existenzieller Quantor: Ist `P : A → Prop` ein Prädikat, so ist
`∃ a : A, P a` die Aussage, dass ein Element `a` in `A` (genauer: vom Typ `A`)
existiert, für das die Aussage `P a` wahr sei.  Eine reine Existenzaussage lässt sich
zum Beispiel als `∃ a : A, true` formulieren.

Um eine Aussage der Form `∃ a : A, …` zu beweisen, konstruiert man ein geeignetes Element `a` und
nutzt dann die `use`-Taktik (`use a`).

Eine Annahme der Form `h : ∃ a : A, P a` lässt sich mit
`choose a ha using h` oder `obtain ⟨a,ha⟩ := h` in die Bestandteile `a : A` und `ha : P a`
zerlegen.
-/
DefinitionDoc Exists as "∃"

/-- Existenzieller Quantor: Ist `P : A → Prop` ein Prädikat, so ist
`∃! a : A, P a` die Aussage, dass *genau ein* Element `a` in `A` (genauer: vom Typ `A`)
existiert, für das die Aussage `P a` wahr sei.  Die Aussage hat also zwei Teile: ertens existiert
solch ein `a`, zweitens ist `a` eindeutig.

Um eine Aussage der Form `∃! a : A, …` zu beweisen, konstruiert man ein geeignetes Element `a` und
nutzt dann die `use`-Taktik (`use a`), in der Regel unmittelbar gefolgt von `simp`.
Nach `use a ` and `simp` sollte das Beweisziel folgende Form haben:

`P(a) ∧ ∀ a' : A, P(a') → a' = a`

Eine Annahme der Form `h : ∃! a : A, P a` lässt sich mit

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
`A ∨ B` ("oder") ist die Aussage mindestens eine der Aussagen `A`, `B` wahr ist.
-/
DefinitionDoc Or as "∨"

/--
Für `n : ℕ` bedeutet `Prime n`, dass `n` eine Primzahl ist.
Um mit dieser Definition zu arbeiten, ist es oft hilfreich, sie mit dem Lemma
`prime_def` umzuschreiben.
-/
DefinitionDoc Prime as "Prime"

/-- `(A : Prop)` ist eine beliebige Aussage, ohne weitere Angabe, ob diese wahr, falsch oder
nicht beweisbar ist.

Siehe auch `(True : Prop)` und `(False : Prop)` die uneingeschränkt wahre (rsp. falsche)
Aussage.
-/
DefinitionDoc «Prop» as "Prop"

/-- Die Aussage `True : Prop` ist immer wahr. -/
DefinitionDoc True as "True"


/-- Für eine endliche Indexmenge `I : Finset T` ist `∑ i ∈ I, f i` die leansche Schreibweise für die Summe
$\sum_{i\in I} f(i)$.  Du schreibst das Summenzeichen als `\sum`.
 -/
DefinitionDoc Sum as "∑"

/-- Für eine endliche Indexmenge `I : Finset T` ist `∏ i ∈ I, f i` die leansche Schreibweise für das Produkt
$\prod_{i\in I} f(i)$.  Du schreibst das Produktzeichen als `\prod`.
 -/
DefinitionDoc Prod as "∏"
