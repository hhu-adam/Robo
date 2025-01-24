-- Level name : Familien von Mengen

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

#check ⋃ i : fin 2, A
#check ⋂ i : fin 2, A

/- Lemma
Zeige.
-/
example {X : Type*} {A B : set X} : true :=
begin
  trivial,
end

