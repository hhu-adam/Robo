import init.data.set
import init.default
import data.set.finite
import data.multiset.finset_ops
import tactic

/-Hier geht es ersten darum, den Unterschied zwischen
  ‘set U‘ und ‘finset U‘ einzuf ̈uhren.
  F ̈ur ‘finset U‘ sind diese Aufgaben dann alle praktisch trivial.
  F ̈ur ‘(S : set U)‘, muss man die Annahme ‘[finite S]‘
  hinzuf ̈ugen, dann werden diese Aufgaben interessanter.-/

/-Nr.1 Jede endliche Vereinigung endlicher Menge
       ist wieder endlich.-/

/-Nr.2 Die Potenzmenge einer endlichen Menge
       ist wieder endlich.-/

/-Nr.3 Ist M endlich und nicht leer, so sind die Menge
       P0(M ) ⊂ P(M ) der Teilmengen, die aus einer
       geraden Anzahl von Elementen bestehen, und die Menge
       P1(M ) der Teilmengen, die aus einer
       ungeraden Anzahl von Elementen bestehen,
       gleich m ̈achtig.-/

/-Nr.1-/
example (M : set (set ℤ) ) (h1 : set.finite M)
        (h2 : ∀ m ∈ M , set.finite m)
       :
       (set.finite (set.sUnion M)):=
begin
       apply set.finite.sUnion h1,
       apply h2,
end

#check fintype

example (N : set ℕ ) [h1 : N.finite]
        (A : N  → set ℤ ) (h2 : ∀ i : N, set.finite (A i))
       :
       set.finite (⋃ i : N, (A i)) :=
begin
  -- Das ist um zwischen `set.finite N` (i.e. `N.finite`) und `finite N` hin und
  -- her zu wechseln. Du könntest alternative auch einfach `[h1: finite N]` oben
  -- schreiben
  haveI : finite N := set.finite.to_subtype h1,

  apply set.finite_Union,
  exact h2,

end


example (A B : finset ℤ)
       :
       (A ∪ B : finset ℤ) :=
begin

end



variables {U : Type*}

open set
variable M : set U

example (h : M.finite) : (𝒫 M).finite :=
begin
  -- Nehme aus `h` tatsächlich eine endliche Menge `M_fin`.
  cases h.exists_finset_coe with M_fin h_M_fin,

  -- This step is somewhat akward, one needs to turn `coe : finset → set` into an `embedding`
  -- To apply it to each subset of `M_fin.powerset`.
  set P := finset.map ⟨coe, finset.coe_injective⟩ M_fin.powerset,

  apply finite.of_finset P,

  intro S,
  split,
  {
    sorry
  },
  { -- Hint: wenn du an eine Stelle kommst, an der du `... = S` hast,
    -- wobei `S ⊆ M` eine Teilmenge ist, dann kannst du mit `have k : S.finite := ...` beweisen
    -- (mit `finite.subset`) und dann folgende Taktik benutzen:
    -- `lift S to finset U using k,`
    -- Das ersetzt dann `S` durch `↑S` wobei dann `S` neu ein `finset` ist anstatt ein `set`.
    sorry
  }
end

/-
Alternativ könnte man `variable M : finset U` definieren. `finset` is eine
endiche Menge und per Definition ist dann `M.powerset` wieder ein `finset`.

Ein `finset` kann mit `(M : set U)` oder `↑M` in ein `set` coerced werden.
-/
