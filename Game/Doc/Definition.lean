import GameServer.Commands

/-! ## Definitions -/



/--
Eine Funktion `f` is injektiv wenn:

```
∀ a b, f a = f b → a = b
```
-/
DefinitionDoc Function.Injective as "Injective"



/--
Eine Funktion `f` is surjektiv wenn:

```
∀ b, ∃ a, f a = b
```
-/
DefinitionDoc Function.Surjective as "Surjective"



/--
Eine Funktion `f` is bijectiv wenn sie injektiv und surjektiv ist.
-/
DefinitionDoc Function.Bijective as "Bijective"



/--
`f` ist strikt monoton wenn

```
∀ a b, a < b → f a < f b
```
-/
DefinitionDoc Function.StrictMono as "StrictMono"



/--
Anonyme Funktionen kann man mit `fun (x : ℤ) => 2 * x` definieren und
wie andere Objekte verwenden.

Note: `=>` wird in mathlib oft auch `↦` (`\\maps`) geschrieben.
-/
DefinitionDoc Symbol.function as "fun x => _"










-- DefinitionDoc Disjoint as "Disjoint"
-- "
-- "


-- DefinitionDoc Set.preimage as "preimage"
-- "
-- "


-- DefinitionDoc Set.Nonempty as "Nonempty" "

-- `A.Nonemty` ist als `∃ x, x ∈ A` definiert.
-- "


-- DefinitionDoc Symbol.Subset as "⊆" "

-- Auf Mengen (`Set`) ist `A ⊆ B` als `∀x, x ∈ A → x ∈ B` implementiert.

-- Im goal kann man direkt `intro x hx` machen, in einer Annahme, kann man mit `obtain`
-- loslegen.

-- Alternativ kann man mit `rw[Set.subset_def]` die Definition explizit einsetzen.
-- "

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

/-- Universeller Quantor: Ist `P : A → Prop` ein Prädikat, so ist
`∀ a : A, P a` die Aussage, dass die Aussage `P a` für alle `a` in `A`
(genauer: für alle `a` vom Typ `A`) wahr sei.

Um eine Aussage der Form `∀ a : A, …` zu beweisen, wählt man mit `intro a` zunächst ein
beliebiges Element `a`.

Ist `h : ∀ a : A, P a` eine Annahme und `a₀ : A` ein konkretes Element, so ist `h a₀`
eine Notation für `P a₀`.  Man kann auch mit `specialize h a₀` die gegebene Annahme
über alle möglichen `a` zu einer Annahme `h : P a₀` über dieses konkrete `a₀` einschränken.
-/
DefinitionDoc «∀» as "∀"

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
Ungleichheit `x ≠ y` ist definiert als `x = y → False`.
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

/-- `(A : Prop)` ist eine beliebige Aussage, ohne weitere Angabe, ob diese wahr, falsch oder
nicht beweisbar ist.

Siehe auch `(True : Prop)` und `(False : Prop)` die uneingeschränkt wahre (rsp. falsche)
Aussage.
-/
DefinitionDoc «Prop» as "Prop"

/-- Die Aussage `True : Prop` ist immer wahr. -/
DefinitionDoc True as "True"
