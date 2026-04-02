-- Level name : nonempty/nontrivial


-- begin hide
import basics.set_theory.set_001
import data.set.finite
import set_theory.cardinal.basic
import data.set.countable
-- end hide

/-

`∈ ∉ ⊆ ⊂ ⋃ ⋂`
-/

open set

open_locale cardinal

variables {X : Type*} (x : X) (A B : set X)

#check A.nonempty
#check nonempty A
#check insert x A -- {x} ∪ A
#check disjoint A B
#check A ∆ B
#check nontrivial A


/- Lemma
Zeige.
-/
example {X : Type*} {A B : set X} : true :=
begin
  trivial,
end
