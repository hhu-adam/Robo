-- Level name : Externes Produkt

-- begin hide
import vectorspace.submodule.sum_prod_3
-- end hide


universe u

variables {K : Type*} [field K]

/-
Eine Familie von Vektorräumen schreibt man erst einmal als Funktion einer Indexmenge `ι`.
-/

variables {ι : Type u} {V : ι → Type u}

/-
Für einen einzelnen Vektorraum würde man jetzt Instanzen `[add_comm_monoid V] [module K V]`
definieren. Lean-Instanzen-Manager versteht hier `∀`-Ausdrücke:
-/

variables [∀i, add_comm_monoid (V i)] [∀i, module K (V i)]

/-
Ein externes Produkt von Vektorräumen schreibt man einfach mit `\Pi`, also `Π i, V i`.

Lean kann aus den Ausdrücken oben dann automatisch herausfinden, dass `Π i, V i`
ein `K`-Vektorraum ist:
-/
example : module K (Π i, V i) := infer_instance

variables {U : Type*} [add_comm_monoid U] [module K U]

def my_prod_map [Π i, add_comm_monoid (V i)] [Π i, module K (V i)]
  (f : Π i, U →ₗ[K] (V i)) : U →ₗ[K] (Π i, V i) :=
{ to_fun := λv i, f i v,
  map_add' :=
  begin
    intros,
    funext,
    simp,
  end,
  map_smul' := 
  begin
    intros,
    funext,
    simp,
  end }

/- Lemma
Sei `U` ein `K`-Vektorraum und `fᵢ : U → Vᵢ` eine Familie von `K`-lineare Abbildungen
in `K`-Vektorräume. Dann gibt es genau eine Abbildung `f : U → (Π i, V i)`, die mit
allen kommutiert.

-/
example 
     (f : Π i, U →ₗ[K] (V i)) :
  ∃! (g : U →ₗ[K] (Π i, V i)), (∀ i v, f i v = g v i) :=
begin
  let g := my_prod_map f,
  use g,
  constructor,
  { simp,
    intros,
    refl },
  { intros g' h,
    apply linear_map.ext,
    intro x,
    change (λ i, g' x i) = λ i, f i x, -- Wieso?
    funext,
    symmetry,
    apply h,
  }
end