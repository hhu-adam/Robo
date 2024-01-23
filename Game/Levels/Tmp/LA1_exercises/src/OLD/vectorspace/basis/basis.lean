-- Level name : Basis

import vectorspace.submodule.generating_set
import vectorspace.basis.lin_indep

notation `ℝ²` := fin 2 → ℝ

/- Lemma
Zeige, dass `![1, 0], ![1, 1]` den ganzen `ℝ`-Vektorraum `ℝ²` aufspannt.
-/
noncomputable def my_basis : basis (fin 2) ℝ ℝ² :=
begin
  apply basis.mk,
  exact my_basis_lin_indep,
  exact my_basis_generates,
end

-- begin hide
-- import data.matrix.notation
-- import data.real.basic
-- import analysis.inner_product_space.pi_L2
-- import linear_algebra.std_basis

-- abbreviation vector_space (K : Type*) (M : Type*) [field K] [add_comm_group M] := module K M

-- -- Matrix notation

-- notation `ℚ²` := fin 2 → ℚ -- euclidean_space ℝ (fin 2)
-- notation `ℚ³` := fin 3 → ℚ -- euclidean_space ℝ (fin 2)
-- notation `ℚ^(` n `)` := (fin n) → ℚ -- euclidean_space ℝ (fin 2)
-- notation `ℚ^(` j, i `)` := matrix (fin j) (fin i) ℚ -- euclidean_space ℝ (fin 2)

-- -- #check !![1, 1; 1, (1 : ℝ)]
-- -- #check { ![(1:ℝ), 1, 1], ![(0:ℝ), 2, -1] } -- is this a vector?

-- -- #check matrix (fin 2) (fin 3) ℝ

-- noncomputable example : vector_space ℚ ℚ² := infer_instance

-- #check pi.basis_fun ℚ²

-- #print vector_space

-- #check ℚ²

-- #check ![(1 : ℚ), 1]

-- #check !![[(1 : ℚ), 1], [3, 4]]

-- example : ℚ² := ![1, 1]
-- example : ℚ² := ![1, 1]

-- def twice : ℚ² →ₗ[ℚ] ℚ² :=
-- { to_fun := λx, 2 • x,
--   map_add' := by simp,
--   map_smul' := by simp }


-- #check twice (![1, 1] : ℚ²)

-- open_locale matrix

-- #check real.division_ring

-- def A : ℚ^(3,2) := ![![ 2, 3],
--                      ![ 0, 1],
--                      ![-1, 0]]
 
-- def B : ℚ^(5,3) := !![ 2, 3.5, 1  ;
--                        0, 1  , 4  ;
--                       -1, 0.6, 8  ;
--                        3, 3  , 3.4;
--                        0, 9  , 1  ]

-- def C : ℚ^(3,3) := ![![ 2, 3, 4],
--                      ![ 0, 1, 3],
--                      ![-1, 0, 1]]

-- def x : ℚ² := ![4, 2]

-- #eval (B ⬝ A)

-- #check C⁻¹ -- Pseudo-inverse of a square matrix

-- #eval matrix.mul_vec (B ⬝ A) x

-- #check !![(2 : ℝ), 3; 0, 1; 1, 0]

-- #check matrix.to_lin _ _

-- example : ![![1, 0, 0], ![0, 2, 0], ![0, 0, 3]] 0 = ![1, 0, 0] := rfl
-- example (f g : (fin 3) → ℚ²) (x : fin 3) (h : f = g) : f x = g x := congr_fun h x
-- /- Lemma
-- Beweise.
-- -/
-- example : true :=
-- begin
--   trivial,
-- end


-- def V : fin 3 → ℚ³ := ![![1, 0, 0], ![0, 2, 0], ![0, 0, 3]]

-- #reduce V 1 0

-- lemma V_lin_independent : linear_independent ℚ V :=
-- begin
--   rw fintype.linear_independent_iff,
--   intros c h j,

--   rw fin.univ_succ at h,
--   simp only [function.embedding.coe_fn_mk, eq_self_iff_true, not_true,
--     not_false_iff, finset.cons_eq_insert, finset.sum_insert, finset.mem_map,
--     finset.mem_univ, exists_true_left, fin.exists_succ_eq_iff, ne.def,
--     finset.sum_map, fin.sum_univ_two, fin.succ_zero_eq_one,
--     fin.succ_one_eq_two] at h,

--   fin_cases j,
--   {
--     have h' := congr_fun h 0,
--     simp only [pi.add_apply, pi.smul_apply, pi.zero_apply] at h',
--     change c 0 * 1 + (c 1 * 0 + c 2 * 0) = 0 at h',
--     linarith,
--   },
--   {
--     have h' := congr_fun h 1,
--     simp only [pi.add_apply, pi.smul_apply, pi.zero_apply] at h',
--     change c 0 * 0 + (c 1 * 2 + c 2 * 0) = 0 at h',
--     linarith,
--   },
--   {
--     have h' := congr_fun h 2,
--     simp only [pi.add_apply, pi.smul_apply, pi.zero_apply] at h',
--     change c 0 * 0 + (c 1 * 0 + c 2 * 3) = 0 at h',
--     linarith,
--   }, 
-- end


-- -- 


-- /--
-- A family of elements is generating if it spans the entire module. 
-- -/
-- def generating (R : Type*) {M ι : Type*}
--   [ring R] [add_comm_monoid M] [module R M] (V : ι → M) :=
-- ⊤ ≤ submodule.span R (set.range V)

-- @[simp] lemma mem_span_range (R : Type*) {M ι : Type*}
--   [ring R] [add_comm_monoid M] [module R M] (V : ι → M) (i : ι) :
--   V i ∈ submodule.span R (set.range V) :=
-- begin
--   apply submodule.subset_span,
--   simp only [set.mem_range_self],
-- end

-- lemma V_generating : generating ℚ V :=
-- begin
--   rw generating,
--   intros w h2,

--   have q : w 0 • V 0 + (w 1 / 2) • V 1 + (w 2 / 3) • V 2 = w :=
--   begin
--     apply funext,
--     intro i,
--     fin_cases i,
--     { change w 0 * 1 + (w 1 / 2) * 0 + (w 2 / 3) * 0 = w 0,
--       simp },
--     { change w 0 * 0 + (w 1 / 2) * 2 + (w 2 / 3) * 0 = w 1,
--       simp },
--     { change w 0 * 0 + (w 1 / 2) * 0 + (w 2 / 3) * 3 = w 2,
--       simp }
--   end,

--   rw ←q,
--   --simp [submodule.add_mem, submodule.smul_mem],

--   simp [submodule.add_mem, submodule.smul_mem],
-- end


-- lemma V_size : fintype.card (fin 3) = finite_dimensional.finrank ℚ (fin 3 → ℚ) :=
-- begin
--   simp only [fintype.card_fin, finite_dimensional.finrank_fin_fun],
-- end

-- #check submodule.eq_top_iff'

-- noncomputable def my_basis := basis.mk V_lin_independent V_generating

-- #check basis_of_linear_independent_of_card_eq_finrank V_lin_independent V_size

--  --rw ←basis.sum_repr (pi.basis_fun ℚ (fin 3)) w,







































-- variables {R V : Type*} [ring R] [add_comm_monoid V] [module R V]
-- variables {v : V} {n : ℕ} {b : fin n → V}

-- lemma L1 (h : v ∈ span R (b '' set.univ)):
--   ∃ (coef : fin n →₀ R), v = ∑ i, (coef i) • (b i) :=
-- begin
--   rw [finsupp.mem_span_image_iff_total R] at h,
--   rcases h with ⟨coef, h₁, h₂⟩,
--   use coef,
--   rw ←h₂,
--   rw finsupp.total_apply,
--   apply finsupp.sum_fintype,
--   simp
-- end

-- lemma L2 (h : v ∈ span R (set.range b)) :
--   ∃ (coef : fin n →₀ R), v = ∑ i, (coef i) • (b i) :=
-- begin
--   rw [←set.image_univ] at h,
--   exact L1 h,
-- end

-- lemma L3 (h : v ∈ span R (set.range b)) :
--   ∃ (coef : fin n → R), v = ∑ i, (coef i) • (b i) :=
-- begin
--   cases L2 h with coef h,
--   exact ⟨coef, h⟩,
-- end

-- #check finsupp.range_total
-- #check finsupp.mem_span_iff_total

-- lemma mem_span_range_iff_exists_sum :
--   v ∈ span R (set.range b) ↔ ∃ (coef : fin n →₀ R), ∑ i, (coef i) • (b i) = v :=
-- begin
--   rw [←finsupp.range_total, linear_map.mem_range],
--   simp_rw finsupp.total_apply,
--   -- TODO: `simp_rw` can't instantiate new goals, is there a better way to do this?
--   have H : ∀ i, (λ (i : fin n) (a : R), a • b i) i 0 = 0 := by simp,
--   simp_rw finsupp.sum_fintype _ _ H,
-- end

-- lemma mem_span_image_iff_exists_sum  :
--   v ∈ span R (b '' set.univ) ↔ ∃ (coef : fin n →₀ R), ∑ i, (coef i) • (b i) = v :=
-- begin
--   simp,
--   rw mem_span_range_iff_exists_sum,
-- end

-- lemma mem_span_range_iff_exists_sum'  :
--   v ∈ span R (set.range b) ↔ ∃ (coef : fin n → R), ∑ i, (coef i) • (b i) = v :=
-- begin
--   rw mem_span_range_iff_exists_sum,
--   constructor,
--   { intro h,
--     cases h with coef h,
--     exact ⟨coef, h⟩ }, -- TODO: This looks suspiciously overcomplicated.
--   { intro h,
--     cases h with coef h,

--     -- TODO: The map `fin n → R` should define a map `fin n →₀ R`.
--     -- I don't understand this but Lean seems to :P
--     lift coef to fin n →₀ R using ⟨fintype.of_finite ↥(function.support coef)⟩,

--     exact ⟨coef, h⟩ }
-- end



-- lemma xx2 : linear_independent ℝ ![![(1: ℝ), 0], ![1, 1]] :=
-- begin
--   sorry
-- end

-- #check basis.mk xx2 xx1

-- noncomputable def my_basis : basis (fin 2) ℝ (fin 2 → ℝ) := basis.mk xx2 xx1

-- #check coe_fn my_basis






-- -- example {B : finset V} {v : V} :
-- --   v ∈ span R (B : set V) ↔ (∃ (coef : V → R), ∑ i in B, coef i • i = v) :=
-- -- begin
-- --   constructor,
-- --   {
-- --     intro h,
    
-- --     let x := (finsupp.mem_span_image_iff_total _).1,
    
-- --   }, sorry

-- --   --rw mem_span_finset,
-- -- end

-- -- #check mem_span_finset




-- -- -- TODO: regard `set.range b` as `finset`

-- -- example : fintype (fin n) := fin.fintype n

-- -- -- OK this is good:
-- -- example (A B : Type*) [fintype A] (f : A → B) : finite (set.range f) := infer_instance
-- -- example : finite (set.range b) := infer_instance

-- -- noncomputable instance fintype_range : fintype (set.range b) :=
-- -- by refine fintype.of_finite (set.range b)

-- -- example : decidable_eq (fin n) := infer_instance
-- -- #check fintype.finset_equiv_set

-- -- def finset_range : finset V :=
-- -- { val := _,
-- --   nodup := _ }

-- --   #check finset.set_of_mem


-- -- -- Was will ich?
-- -- -- `(set.range b : set V) --> (??? : finset V)`

-- -- #check (set.range b : set V).univ


-- -- #check (@finset.univ (set.range b) _ : set (set.range b))

-- -- def range_equiv_finset_univ : (set.range b) = (@finset.univ (set.range b) _ : set V) := sorry

-- -- #check finset.image _ (set.range b : finset V)

-- -- #check (⊤ : finset (set.range b))

-- -- example : v ∈ span R (set.range b) ↔ ∃ (coef : fin n → R), v = ∑ i, (coef i) • (b i) :=
-- -- begin
-- --   rw range_equiv_finset_univ b,
-- --   rw span_range_eq_supr,
-- --   constructor,
-- --   {
-- --     intro h,
-- --     rw submodule.mem_supr at h,

-- --   },
-- --   sorry
-- -- end















































-- -- notation `ℝ²` := fin 2 → ℝ

-- -- open submodule -- damit man `span` anstatt `submodule.span` schreiben kann

-- -- /-
-- -- Eine Teilmenge `M = {m₁, m₂, ..., mₖ} ⊆ V` eines `K`-Vektorraums `V` ist
-- -- ein "Erzeugendensystem" wenn die Hülle von `M` ganz `V` aufspannt.

-- -- In Lean kann man das als `span K M = ⊤` schreiben, aber standardmässig wird
-- -- immer `⊤ ≤ span K M` gewählt, da die andere Richtung trivial ist.
-- -- -/

-- -- /- Lemma : no-side-bar
-- -- Zeige, dass `![1,0], ![1, 1]` ganz `ℝ²` aufspannt.
-- -- -/

-- -- def v : fin 2 → ℝ² := ![![1, 0], ![1, 1]]

-- -- variables {R V ι : Type*} [ring R] [add_comm_monoid V] [module R V]

-- -- example {r v : V} {s : set V} (h : r ∈ span R s) (h2 : v ∈ span R s):
-- --   module R (span R s) :=
-- --   infer_instance


-- -- lemma mem_span_range {n : ℕ} (x : fin n) (b : fin n → V) : b x ∈ span R (set.range b) :=
-- -- begin
-- --   apply subset_span,
-- --   simp,
-- -- end

-- -- lemma xxx {n : ℕ} (b : fin n.succ → V) :
-- --   (set.range (λ(i : fin n), b i.succ)) ⊆ (set.range b) :=
-- -- begin
-- --   -- Automated by `tidy`.
-- --   intros x hx,
-- --   cases hx with i h,
-- --   induction h,
-- --   simp only [set.mem_range_self],
-- -- end

-- -- example {U U' : set V} (h : U ≤ U') : (span R U) ≤ span R U' := span_monotone h
-- -- example {U U' : submodule R V} {x : V} (h2: x ∈ U) (h : U ≤ U') : x ∈ U' := h h2

-- -- section sum_mem

-- -- variables {M A B : Type*}

-- -- variables [monoid M] [set_like B M] [submonoid_class B M] {S : B}

-- -- @[to_additive "Sum of elements in an `add_submonoid` of an `add_comm_monoid` indexed by a `finset`
-- -- is in the `add_submonoid`."]
-- -- lemma prod_mem' {M : Type*} [comm_monoid M] [set_like B M] [submonoid_class B M]
-- --   {n : ℕ} {f : fin n → M} (h : ∀(c : fin n), f c ∈ S) :
-- --   ∏ (c : fin n), f c ∈ S :=
-- -- begin
-- --   sorry
-- -- end
-- -- --multiset_prod_mem (t.1.map f) $ λ x hx, let ⟨i, hi, hix⟩ := multiset.mem_map.1 hx in hix ▸ h i hi

-- -- end sum_mem


-- -- -- example (n : ℕ) (v : V) (b : fin n → V) (coeff : fin n → R)
-- -- --   (h : v = ∑ i : fin n, (coeff i • b i)) : v ∈ span R (set.range b) :=
-- -- -- begin
-- -- --   rw h,

-- -- --   let f : fin n → V := λ i, coeff i • b i,
-- -- --   convert_to ∑ (i : fin n), f i ∈ span R (set.range b),

-- -- --   apply @sum_mem' _ (span R (set.range b)) V _ _ _ n f,

-- -- --   intro i,
-- -- --   apply subset_span,
  
-- -- --   change coeff i • b i ∈ set.range b,
-- -- --   have := (span R (set.range b)).smul_mem (coeff i),
-- -- -- end


-- -- #check span.repr 
-- -- #check mem_span_finset
-- -- #check span_range_eq_supr -- Then express as internal sum.


-- -- lemma xx {v : V} {b : ι → V} (h : v ∈ span R (set.range b)) :
-- --   ∃ (coef : ι →₀ R), v = ∑ᶠ i, (coef i • b i) :=
-- -- begin

-- -- end

-- -- example {v : V} {n : ℕ}  {b : fin n → V} (h : v ∈ span R (set.range b)) :
-- --   (∃ (coef : fin n → R), v = ∑ (i : fin n), coef i • b i) :=
-- -- begin

-- -- end

-- -- #check set_like.ext_iff.1
-- -- #check finsupp.span_eq_range_total _ _

-- -- noncomputable def my_repr (w : set V) {x : V} (x ∈ span R w) : w →₀ R :=
-- -- ((finsupp.mem_span_iff_total _ _ _).mp x.2).some

-- -- variables {x : V} {n : ℕ} {b : fin n → V}
-- -- #check @mem_span_finset R V _ _ _ (set.range b)

-- -- lemma mem_span_iff_sum_coeff {v : V} {n : ℕ} {b : fin n → V} :
-- --   v ∈ span R (set.range b) ↔ ∃ (coef : fin n → R), v = ∑ i, (coef i) • (b i) :=
-- -- begin
-- --   --rw submodule.span_range_eq_supr,
-- --   constructor,
-- --   { intro h,

-- --     let coef : fin n → R := λ i, (span.repr R (set.range b) ⟨v, h⟩) ⟨b i, by simp⟩,
-- --     use coef,
-- --     simp_rw [coef],
    
    

-- --     -- Most statements are about `∑ i, f i` and it can't match `coef i • b i` with `f? i`.
-- --     change ∃ (coef : fin n → R), v = ∑ (i : fin n), (λ j, coef j • b j) i,

-- --     simp_rw ←finsum_eq_sum_of_fintype,



-- -- --rw finsupp.span_eq_range_total R (set.range b),
-- --     cases (finsupp.mem_span_iff_total R _ _ ).mp h with coef' h,

-- --     let coef := (λ (i : fin n), coef' ⟨b i, ⟨i, rfl⟩⟩),
-- --     use coef,

-- --     cases xx h with coef h,
-- --     use coef,
-- --     rw h,
-- --     rw finsum_eq_sum_of_fintype,
-- --   },
-- --   { intro h,
-- --     cases h with x hx,
-- --     rw hx, clear hx v,
-- --     induction n with n hn,
-- --     { simp },
-- --     { rw fin.sum_univ_succ,
-- --       apply (span R (set.range b)).add_mem,
-- --       { apply (span R (set.range b)).smul_mem,
-- --         apply mem_span_range },
-- --       { apply span_mono (xxx b),
-- --         refine (@hn (λi, b i.succ) (λi, x i.succ)) }}}
-- -- end

-- -- example : ⊤ ≤ span ℝ (set.range ![![(1: ℝ), 0], ![1, 1]]) :=
-- -- begin
-- --   intros v hv,

-- --   rw span_range_eq_supr,


-- --   rw mem_span_iff_sum_coeff,
-- --   use ![v 0 - v 1, v 1],
-- --   simp,
-- --   funext i,
-- --   fin_cases i;
-- --   simp,
-- -- end



-- end hide