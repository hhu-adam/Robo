-- Level name : Teilmengen

-- begin hide
import basics.set_theory.set_001
import data.set.finite
import set_theory.cardinal.basic
import data.set.countable
-- end hide

/-
Es gibt zwei Arten von Enthalten-Sein in der Mengenlehre. Zuerst ganz simple, wenn `{X : Type*}`
ein beliebiger Typ ist und `(A B : set X)` zwei Mengen, dann sagt `A ⊆ B` (`\sub`) dass `A` in `B`
enthalten ist. `A ⊂ B` bedeutet strickte Inklusion, i.e. `A ⊆ B ∧ ¬ B ⊆ A`.

`Aᶜ` (`\^c`) is übrigens das Komplement.

Elemente von `A` zu nehmen ist etwas filigraner: Man nimmt ein Element `(x : X)` vom Typ `X` und sagt
dann mit `x ∈ A`, dass `x` in `A` liegt.

Der Ausdruck `(x : A)` wäre falsch!

Oft, wie zum Beispiel bei `∃`, kennt Lean die Schreibweise `∃ x ∈ A, P x`, welche mehr oder weniger
eine Abkürzung für `∃ (x : X) (h : x ∈ A), P x` ist.
-/

open set

variables {X : Type*} (x : X) (A B : set X)

/- Lemma
Zeige.
-/
example {X : Type*} {A : set X} (h : Aᶜ ⊆ A) : A = univ :=
begin
  apply subset.antisymm,
  simp only [set.subset_univ],
  intros x hx,
  by_cases h4 : x ∈ Aᶜ,
  exact mem_of_subset_of_mem h h4,
  rw ←not_mem_compl_iff,
  exact h4,
end

example {X : Type*} {A B : set X} (h : A ⊂ B) : ∃ x, x ∈ B \ A :=
begin
  cases h with h₁ h₂,
  rw subset_def at h₂,
  rw not_forall at h₂,
  cases h₂ with x hx,
  use x,
  rw not_imp at hx,
  rw mem_diff,
  exact hx,
end
