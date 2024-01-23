-- Level name : Potenzmenge

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

#check 𝒫 A

/- Lemma
Zeige.
-/
example {X : Type*} {A B : set X} : true :=
begin
  trivial,
end
