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
∀ a, ∃ b, f a = b
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

-- Im goal kann man direkt `intro x hx` machen, in einer Annahme, kann man mit `rcases`
-- loslegen.

-- Alternativ kann man mit `rw[Set.subset_def]` die Definition explizit einsetzen.
-- "
