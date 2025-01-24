import Mathlib.Topology.Instances.Real
open BigOperators Function Set Filter Topology TopologicalSpace

/- # Topology via Filters
inspired by MIL and Patrick Massot's slides:
https://www.imo.universite-paris-saclay.fr/~patrick.massot/topology.pdf
-/


/- # Convergence -/


/-
In topology, one of basic concepts is that of convergence.

Mostly we are familiar with convergence of sequences: Suppose `X` is a topological space, and `f` a sequence in `X`, and `x ∈ X`.  We say that `f`
converges to `x` if for any open set `U ∋ x`, there exists an `N` such that if `n > N`, then an `x n ∈ U`. Another way of saying the same thing: for any open set `U ∋ x`, no matter how small, the neighborhood sets `F_N := {x n | n > N}` eventually lie in `U`.

## Observation 1:
So, we only requires knowledge of which sets contain at least one of the `F_N`. For example, if we alter the sequence at finitely many places, it doesn’t change its convergence properties because it doesn’t change which sets contain some `F_N`.

We also talk about convergence of functions:
Say `f : ℝ → ℝ`. Consider the limit expression "`f x` tends to `y₀` as `x` tends to `x₀`".

There are many variants of limits:
* the limit of `f(x)` as `x` tends to `x₀ : ℝ`
* the limit of `f(x)` as `x` tends to `∞` or `-∞`
* the limit of `f(x)` as `x` tends to `x₀⁻` or `x₀⁺` (upper and lower limits)
* variations of the above with the additional assumption that `x ≠ x₀`.

This gives 8 different notions of behavior of `x`.
Similarly, the value `f(x)` can have the same behavior:
`f(x)` tends to `∞`, `-∞`, `x₀`, `x₀⁺`, ...

This gives `64` notions of limits.

This problem an get worse due to the complexity of various operations on functions:
For instance, when proving that limits compose: if
`f x` tends to `y₀` when `x` tends to `x₀` and
`g y` tends to `z₀` when `y` tends to `y₀` then
`(g ∘ f) x` tends to `z₀` when `x` tends to `x₀`.
This lemma has 512 variants.

## Observation 2:
We don't want to prove 512 variations of the lemmas about composition of limits.

Observation 1 and 2 suggest that we need a more abstract way to talk about limits. The solution is the concept of __filter__. Filters provide us with the linguistic tools to talk about limits in a general way.


If `X` is a type, a filter `F : Filter X` on `X` is a
collection of sets `F.sets : Set (Set X)` satisfying the following axioms:
1. `univ ∈ F.sets` (contains the universal set)
2. If `U ∈ F.sets` and `U ⊆ V` then  `V ∈ F.sets` (upwards closed)
3. If `U, V ∈ F.sets` then `U ∩ V ∈ F.sets` (stable under intersection)

Example:  If `f` is a sequence in `X`, the elementary filter associated to `f` is the set
 `{A ⊂ X | ∃ N, n > N → f n ∈ A}`

We say that a filter `F` in `X` converges to a point `x : X`, if every open set containing `x` is in `F`. Think about what this means in the case of the elementary filter.
-/
section Filter

variable {X Y : Type*} (F : Filter X)

#check (F.sets : Set (Set X)) -- a set of subsets of `X`

#check (F.univ_sets : univ ∈ F.sets) -- contains the universal subset of `X`

#check (F.sets_of_superset : ∀ {U V},
  U ∈ F.sets → U ⊆ V → V ∈ F.sets)  -- upwards closed

#check (F.inter_sets : ∀ {U V},
  U ∈ F.sets → V ∈ F.sets → U ∩ V ∈ F.sets) -- stable under intersection

end Filter



/-
Examples of filters:
-/

/-
`atTop` is the filter representing the limit `→ ∞` on an ordered set; it is generated
by the collection of up-sets `{b | a ≤ b}`, e.g.
`(atTop : Filter ℕ)` is made of sets of `ℕ` containing
`{n | n ≥ N}` for some `N` -/

#check (atTop : Filter ℕ)

#check (atTop : Filter ℝ)

example {s : Set ℝ} :
    s ∈ atTop ↔ ∃ N, ∀ n ≥ N, n ∈ s := by
  exact mem_atTop_sets

#check (Even : Set ℕ)

example : Even ∉ (atTop : Filter ℕ).sets := by
  intro h
  obtain ⟨N, hN⟩ := mem_atTop_sets.mp h
  cases Decidable.em (Even N)
  case
    inl => sorry
  case
   inr => sorry

/- The neighborhood filter `𝓝 x`, made of neighborhoods of `x` in a topological space -/
#check (𝓝 0 : Filter ℝ)


/-

Embedding
Set X ⥤ Filter X

* For each `s : Set X` we have the so-called *principal filter*
  `𝓟 s` consisting of all sets that contain `s`.
  This gives rise to a functor `Set X ⥤ Filter X`.

It is useful to think of a filter on a type `X`
as a generalized element of `Set X`.
* `atTop` is the "set of very large numbers"
* `𝓝 x₀` is the "set of points very close to `x₀`."
-/

section
variable {X : Type*}
#check (𝓟 : Set X → Filter X)
end

example {s t : Set ℝ} : t ∈ 𝓟 s ↔ s ⊆ t :=
  by exact mem_principal


/- Operations on filters -/

/- the *pushforward* of filters generalizes images of sets. -/
example {X Y : Type*} (f : X → Y) : Filter X → Filter Y :=
  Filter.map f

example {X Y : Type*} (f : X → Y) (F : Filter X) (V : Set Y) :
    V ∈ Filter.map f F ↔ f ⁻¹' V ∈ F := by
  rfl

/- the *pullback* of filters generalizes preimages -/
example {X Y : Type*} (f : X → Y) : Filter Y → Filter X :=
  Filter.comap f

/- `Filter X` has an order that turns it into a complete lattice.
The order is reverse inclusion.
Here's how I like to think about it:
`F ≤ F'` means that `F` is "finer" than `F'`. That means any observation about
points of `F'` is also an observation points of `F`.

-/
example {X : Type*} (F F' : Filter X) :
    F ≤ F' ↔ ∀ V : Set X, V ∈ F' → V ∈ F := by
  rfl

/- `Filter.map` and `Filter.comap` form a Galois connection (aka adjunction). -/
example {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :
    Filter.map f F ≤ G ↔ F ≤ Filter.comap f G := by
  exact map_le_iff_le_comap

/- The principal filter `𝓟 : Set X → Filter X` is monotone. -/
example {X : Type*} : Monotone (𝓟 : Set X → Filter X) := by
  exact monotone_principal

/- Using these operations, we can define the **convergence**. -/
def MyTendsto {X Y : Type*} (f : X → Y)
    (F : Filter X) (G : Filter Y) :=
  map f F ≤ G

def Tendsto_iff {X Y : Type*} (f : X → Y)
    (F : Filter X) (G : Filter Y) :
    Tendsto f F G ↔ ∀ S : Set Y, S ∈ G → f ⁻¹' S ∈ F := by
  rfl

/- A sequence `u` converges to `x` -/
example (u : ℕ → ℝ) (x : ℝ) : Prop :=
  Tendsto u atTop (𝓝 x)

/- `\lim_{x → x₀} f(x) = y₀` -/
example (f : ℝ → ℝ) (x₀ y₀ : ℝ) : Prop :=
  Tendsto f (𝓝 x₀) (𝓝 y₀)

/- `\lim_{x → x₀⁻, x ≠ x₀} f(x) = y₀⁺` -/
example (f : ℝ → ℝ) (x₀ y₀ : ℝ) : Prop :=
  Tendsto f (𝓝[<] x₀) (𝓝[≥] y₀)
