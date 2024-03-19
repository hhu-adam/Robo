import data.real.basic
import topology.basic
import data.set.function
import order.filter.ultrafilter
import algebra.support
import order.filter.lift
import topology.continuous_function.algebra
import topology.instances.real
import topology.algebra.order.intermediate_value


-- Sei I = [a,b] und f_I-> R stetig mit f(I) untermenge von I
--zz ∃ x ∈ I: f(x)=x

--def stetig (f : _) (x : RR) := ∀ eps, ∃ delta, _

def lok_stetig (f: ℝ → ℝ) (x: ℝ):=
∀ (ε:ℝ), ∃ δ > 0, ∀ (x0: ℝ), |x0-x| < δ → |f(x0)-f(x)| < ε

def stetig (I: set ℝ) (f: ℝ → ℝ ) :=
∀ x ∈ I, lok_stetig f x

--Zwischenwertsatz muss gezeigt werden
/-
example (a b : ℝ) (f : ℝ  → ℝ) (h0 : stetig (set.Icc a b) f) [h1: (set.image f (set.Icc a b) ⊂ (set.Icc a b))]:
∃ (x:(set.Icc a b)), f x = x :=
begin
  let g: λ (x : set.Icc[a b]), x
  intermediate_value_univ g f
end
-/

#check intermediate_value_Icc

lemma nullstelle {a b : ℝ} (j: a ≤ b) {g : ℝ  → ℝ}
  (h0: continuous_on g (set.Icc a b)) (l: (0 : ℝ) ∈ set.Icc (g a) (g b)) :
  ∃ (x : ℝ) (H : x ∈ set.Icc a b), g x = 0 :=
begin
  have h₁ := intermediate_value_Icc j h0,
  library_search,
end

example (a b : ℝ) (j: a ≤ b) (f : ℝ  → ℝ) [h0: continuous_on f (set.Icc a b)] [h1: (set.image f (set.Icc a b) ⊂ (set.Icc a b))]:
∃ (x ∈ (set.Icc a b)), f x = x :=
begin
--Für den Beweis definieren wir eine Funktion, welche aus f und x besteht--
  let g:= λ (x : ℝ), x - f x,
--Wollen zeigen, dass g stetig ist--
  have cg: continuous_on g (set.Icc a b),{
    apply continuous_on.sub,
    apply continuous_on_id,
    apply h0, },
--Wollen zeigen, dass 0 ein Element von [g(a),g(b)] ist--
  have l: ((0: ℝ) ∈ set.Icc (g a) (g b)),
    rw [set.mem_Icc],
    constructor,
    {
    simp,
    rw [set.ssubset_def] at h1,
    rcases h1,
    rw [set.subset_def] at h1_left,
    specialize h1_left (f a),
    simp? at h1_left,
    specialize h1_left (a),
    tauto,},
------------------------------------------------------------------
    {
    simp,
    rw [set.ssubset_def] at h1,
    rcases h1,
    rw [set.subset_def] at h1_left,
    specialize h1_left (f b),
    simp? at h1_left,
    specialize h1_left (b),
    tauto,},
--Wollen jetzt auch zeigen, dass es ein x gibt, wo g(x)=x-f(x)=0 ist--
  have g0: ∃ x ∈ (set.Icc a b), g x = 0,
  { apply nullstelle j cg l, },
--Wollen nur noch zeigen, wenn g(x)=x-f(x)=0 <=> x=f(x)--
  simp only [g] at g0,
  rcases g0 with ⟨x, hx, hx2⟩,
  use x,
  constructor,
  assumption,
  refine eq.symm _,
  refine sub_eq_zero.mp _,
  assumption,
end

#check set.maps_to.restrict
