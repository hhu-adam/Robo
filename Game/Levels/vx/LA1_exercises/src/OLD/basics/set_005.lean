-- Level name : Endliche Mengen

-- begin hide
import basics.set_theory.set_001
import data.set.finite
import set_theory.cardinal.basic
import data.set.countable
-- end hide

/-

-/

open set

variables {X : Type*} (x : X) (A B : set X)

variables (C : finset A) (a : C)
#check finite A
#check fin 2
#check infinite A
#check ({2, 3, 5} : set ℕ) ∪ {4}

/- Lemma
Zeige.
-/
example {X : Type*} {A B : set X} : true :=
begin
  trivial,
end
