-- Level name : 3. Binomis Baukasten

import data.set.finite
import data.real.basic

/-
Comment here
-/

/- Hint : title_of_the_hint
Content of the hint
-/

variables {U : Type*}

open set
variable M : set U

-- begin hide
section scratch

variable N : finset U
#check (powerset ↑N).finite

#check (𝒫 ↑N).finite

#check powerset ↑N

#check N.powerset -- This is by definition already a `finset`

example (M S : set U) (h : M.finite) (g : S ⊆ M) : S.finite :=
finite.subset h g

end scratch
-- end hide


/- Lemma
Description of the lemma
-/
example (h : M.finite) : (𝒫 M).finite :=
begin
  cases h.exists_finset_coe with M_fin h_M_fin,

  -- This step is somewhat awkward, one needs to turn `coe : finset → set` into an `embedding`
  -- To apply it to each subset of `M_fin.powerset`.
  set P := finset.map ⟨coe, finset.coe_injective⟩ M_fin.powerset,

  apply finite.of_finset P,

  intro S,
  split,
  { intro hS,
    simp at ⊢ hS,
    obtain ⟨S_fin, h_S_fin, h_S_fin'⟩ := hS,
    rw [←h_S_fin', ←h_M_fin],
    simp,
    exact h_S_fin,
  },
  { intro hS,
    simp at ⊢ hS,
    lift S to finset U using finite.subset h hS,
    use S,
    rw ←h_M_fin at hS,
    constructor,
    exact finset.coe_subset.mp hS,
    refl,
  }
end

/-
Alternativ könnte man `variable M : finset U` definieren. `finset` is eine
endiche Menge und per Definition ist dann `M.powerset` wieder ein `finset`.

Ein `finset` kann mit `(M : set U)` oder `↑M` in ein `set` coerced werden.
-/


example (a b : ℕ) (h : a < b) (g : b < a) : false := begin
  exact nat.lt_asymm h g,
end

example (a b : ℝ) (h : a < b) (g : b < a) : false := begin
  exact lt_asymm h g,
end
