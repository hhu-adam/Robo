-- Level name : Externe Summe

-- begin hide
import vectorspace.submodule.sum_prod_4
-- end hide


universe u

variables {K : Type*} [field K]
variables {ι : Type u} {V : ι → Type u}
variables [∀i, add_comm_monoid (V i)] [∀i, module K (V i)]

/-
Ein externes Summe von Vektorräumen schreibt man mit `\Pi\0`, also `Π₀ i, V i`.
Das Suffix `_₀` wird in Mathlib häufig dafür verwendet "endlichen Support" zu bezeichnen.

-/
example : module K (Π₀ i, V i) := infer_instance

variables {U : Type*} [add_comm_monoid U] [module K U]

-- :(
variables [decidable_eq ι]
variables [Π (i : ι) (x : V i), decidable (x ≠ 0)]

def my_sum_map (f : Π i, V i →ₗ[K] U) : (Π₀ i, V i) →ₗ[K] U :=
{ to_fun := λ x, x.sum (λ i, (f i)),
  map_add' :=
  begin
    intros,
    funext,
    sorry,
  end,
  map_smul' := 
  begin
    intros,
    funext,
    simp,
    sorry
  end }

/- Lemma
Sei `U` ein `K`-Vektorraum und `fᵢ : Vᵢ → U` eine Familie von `K`-lineare Abbildungen
in `K`-Vektorräume. Dann gibt es genau eine Abbildung `f : (Π₀ i, V i) → U`, die mit
allen kommutiert.

-/
example
     (f : Π i, V i →ₗ[K] U) :
  ∃! (g : (Π₀ i, V i) →ₗ[K] U), (∀ i v, f i v = g (dfinsupp.single i v)) :=
begin
  let g := my_sum_map f,
  use g,
  constructor,
  { simp,
    intros,
    sorry },
  { intros g' h,
    apply linear_map.ext,
    intro x,
    sorry
    -- change (λ i, g' x i) = λ i, f i x, -- Wieso?
    -- funext,
    -- symmetry,
    -- apply h,
  }
end