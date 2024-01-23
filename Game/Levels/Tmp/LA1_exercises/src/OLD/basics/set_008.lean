-- Level name : Kardinalität

-- begin hide
import basics.set_theory.set_001
import data.set.finite
import set_theory.cardinal.basic
import data.set.countable
-- end hide

/-

-/

open set

example : set.finite ({0, 1} : set ℕ) := ({0, 1} : set ℕ).to_finite

example (A : set ℕ) (h: A.finite) (g: ∀ B : finset ℕ, B = ∅) : A = ∅ :=
begin
  lift A to (finset ℕ),
  assumption,
  lift ∅ to (finset ℕ),

end

example : 𝒫 ({0, 1} : set ℕ) = {∅, {0}, {1}, {0, 1}} :=
begin
  have hn := ({0, 1} : set ℕ).to_finite,
  lift {0, 1} to ({0, 1} : finset ℕ) with hn
end


open_locale cardinal

variables {X : Type*} (x : X) (A B : set X)

#check C.card
#check ℵ₀
#check #ℕ 
#check # (univ : set ℕ) 
#check set.countable A
#check set.countable (univ : set ℕ)
#check countable ℕ
#check #A


/- Lemma
Zeige.
-/
example {X : Type*} {A B : set X} : true :=
begin
  trivial,
end
