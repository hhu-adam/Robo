import ring_theory.noetherian
import ring_theory.polynomial.basic
--import data.polynomial.basic
--import data.finset.preimage
--import data.finset.image
--import init.data.set
--import data.set.finite
--import data.set.function
--import data.set.image
--import data.set.basic
--import data.polynomial.degree.definitions
--import algebra.char_p.basic
--import set_theory.zfc.basic
--import data.list.min_max
--import data.finset.card

open polynomial
open_locale polynomial

variables {R : Type} [comm_ring R] [decidable_eq R] [decidable_eq R[X]]

lemma ideal_eq_iff_carrier_eq {R : Type} [comm_ring R] (a : ideal R) (b : ideal R) :
  a = b ↔ a.carrier = b.carrier :=
begin
  constructor, {
    intro h,
    ext,
    rw [h]
  }, {
    intro h,
    rw [← ideal.span_eq a],
    rw [← ideal.span_eq b],
    change ideal.span a.carrier = ideal.span b.carrier,
    exact congr_arg ideal.span h
  },
end

theorem hilbert_basis_theorem [R_noetherian : is_noetherian_ring R] : is_noetherian_ring R[X] :=
begin
  --Behauptung: Sei R ein noetherscher Ring. Dann ist auch R[X] noethersch.
  --Es reicht zu zeigen: Jedes Ideal a ⊴ R[X] ist endlich erzeugt.
  rw [is_noetherian_ring_iff_ideal_fg],
  rw [is_noetherian_ring_iff_ideal_fg] at R_noetherian,
  unfold ideal.fg,
  unfold ideal.fg at R_noetherian,

  --Sei a ⊴ R[X] ein Ideal von R[X].
  intro a,

  --Für k ∈ ℕ sei b(k) ⊆ R die Menge der Leitkoeffizienten der Polynome f ∈ a mit deg(f) ≤ k.
  --Betrachte dazu die Menge a(k) = {f ∈ a | deg(f) ≤ k} ⊆ a. Dann ist die Abbildung
  --
  --                      η(k) : a(k) → R, f ↦ leading_coeff(f)
  --
  --ein Modulhomomorphismus. Damit ist b(k) := im η(k) ⊴ R insbesondere ein Ideal von R. Die
  --Abbildung η(k) ist bereits implementiert als "polynomial.lcoeff R k".
  let η := lcoeff R,
  let b : ℕ → ideal R := λ k, submodule.map (η k) (a.degree_le ↑k),

  --Für jedes k ∈ ℕ besitzt b(k) ein Urbild unter η(k) in a(k).
  have bk_has_preimage : ∀ k : ℕ, ∀ y : R, ∃ x, y ∈ (b k) → x ∈ a.degree_le ↑k ∧ (η k) x = y, {
    intro k,
    intro y,
      by_cases hy : y ∈ b k,
      { rw [submodule.mem_map] at hy,
        rcases hy with ⟨x,hx⟩,
        use x,
        intro,
        assumption,
        },
      { use default,
        }
  },

  --Sei μ : ℕ → R → R[X] eine Rechtsinverse von η(k), das heißt für alle k ∈ ℕ und y ∈ R
  --gilt (η(k) ∘ μ)(y) = y.
  let μ : ℕ → R → R[X] := λ k y, (bk_has_preimage k y).some,

  --unnötig?
  have hμ : ∀ (k : ℕ), ∀ (y : R), y ∈ (b k) → (μ k y) ∈ (a.degree_le ↑k) ∧ (η k) (μ k y) = y,
    { intro k,
      intro y,
      exact (bk_has_preimage k y).some_spec, },

  --Als Ideal von R ist jedes b(k) endlich erzeugt. Insbesondere existiert für jedes k ∈ ℕ eine endliche
  --Menge F(k) = {f1,...,fn} ⊆ a von Polynomen, so dass die Leitkoeffizieten dieser Polynome b(k) erzeugen.
  have exists_F : ∀ (k : ℕ), ∃ (F : finset (R[X])), (↑F : set _) ⊆ a.carrier ∧ (b k) = ideal.span ((η k) '' F), {
    --Sei S eine erzeugende Menge von b(k).
    intro k,
    rcases R_noetherian (b k) with ⟨S,hS⟩,

    --Offenbar gilt S ⊆ b(k).
    have S_subset_bk : ↑S ⊆ (b k).carrier,
    { rw [← hS], apply ideal.subset_span, },

    --Wähle als F(k) nun "einfach" μ(S).
    use S.image (μ k),
    constructor,
    { intros x hx,
      norm_cast at hx,
      rw [finset.mem_image] at hx,
      rcases hx with ⟨y, hy, hxy⟩,
      subst hxy,
      apply (hμ k y (S_subset_bk hy)).1.2, },
    { rw [← hS],
      congr,
      apply subset_antisymm,
      { intros y hy,
        rw set.mem_image,
        use μ k y,
        constructor,
        apply finset.mem_image_of_mem,
        apply hy,
        exact (hμ k y (S_subset_bk hy)).2, },
      { intros x hx,
        rw set.mem_image at hx,
        rcases hx with ⟨y, hy, hxy⟩,
        norm_cast at hy,
        rw [finset.mem_image] at hy,
        subst hxy,
        rcases hy with ⟨x, hx, hxy⟩,
        subst hxy,
        rw (hμ k x (S_subset_bk hx)).2,
        exact hx,
      } },
  },

  let F := λ k, (exists_F k).some,
  have hF := λ k, (exists_F k).some_spec,

  --Sei bb die Vereinigung aller b(k).
  let bb : ideal R := ⨆ (k : ℕ), (b k),

  --Als Ideal von R ist auch bb eine endlich erzeugt. Folglich existiert eine Menge FF ⊆ a von Polynomen,
  --deren Leitkoeffizienten bb erzeugen. Sei d der höchste Grad der Polynome in FF. Dann gilt ⟨η(d)(FF)⟩ = bb.
  have exists_FF : ∃ (k : ℕ), ∃ (FF : finset (R[X])), (↑FF : set _) ⊆ a.carrier ∧ bb = ideal.span ((η k) '' FF), {

    rcases R_noetherian bb with ⟨S,hS⟩,

    have S_subset_bk : ∃ (k : ℕ), ↑S ⊆ (b k).carrier, {
      by_contra c,
      push_neg at c,
      sorry --Schwierig, aber machbar.
    },

    rcases S_subset_bk with ⟨k,hk⟩,

    have bb_eq_bk : bb = (b k), {
      suffices : bb ≤ b k ∧ bb ≥ b k, {
        rw [ideal_eq_iff_carrier_eq],
        rw [set.subset.antisymm_iff],
        assumption,
      },
      constructor, {
        rw [←hS],
        rw [ideal.span_le],
        assumption
      }, {
        change b k ≤ ⨆ (k : ℕ), b k,
        simp,
        rw [le_supr_iff],
        intros I hI,
        exact (hI k)
      },
    },

    use k,
    rcases exists_F k with ⟨FF,hFF⟩,
    use FF,
    rw [bb_eq_bk],
    assumption
  },

  rcases exists_FF with ⟨K, FF, hFFA, hFF⟩,

  --Wenn K minimal gewählt wurde, dann ist K der höchste Grad der Polynome in FF.
  --Aber man kann auch K beliebig groß genug wählen. Dann sei d = max{ deg(f) | f ∈ FF }.

  -- Note: `match` statements hatten wir nicht, aber ist eine gute Art, eine Fallunterscheidung zu machen.
  let d : nat :=
    match (FF.image polynomial.degree).max with
    | (some (some d)) := d
    | _ := 0 -- Note: in allen anderen Fällen
    end,

  --let d := finset.max (finset.image polynomial.degree FF),
  --let d : ℕ := (FF.image polynomial.nat_degree).max.unbot sorry,

  have hFF₂ : bb = ideal.span (⇑(η d) '' ↑FF), {
    sorry --wlog_sorry
  },

  --Konstruiere nun FU = F(0) ∪ F(1) ∪ ... ∪ F(d-1) ∪ FF ⊆ a_d. Als endliche Vereinigung von
  --endlichen Mengen ist FU endlich. Sei ferner aa = ⟨FU⟩ ⊴ R[X] ein endlich erzeugtes Ideal.
  let FU : finset R[X] := FF ∪ finset.bUnion (finset.Iio d) F,
  let aa : ideal R[X] := ideal.span ↑FU,

  --Wir zeigen nun, dass a gleich aa ist.
  --Daraus folgt die Behauptung.
  suffices : a = aa, {
    use FU,
    rw [this] at *
  },

  --Zu erst ein paar Kleinigkeiten.

  --Es gilt FF ⊆ a und F(k) ⊆ a für jedes k ∈ ℕ, also gilt auch FU ⊆ a.
  have FU_subset_a : ↑FU ⊆ a.carrier, {
    change ↑(FF ∪ (finset.Iio d).bUnion F) ⊆ a.carrier,

    --Es reicht zu zeigen, dass FF ⊆ a und ((finset.Iio d).bUnion F) ⊆ a gilt.
    suffices : ↑FF ⊆ a.carrier ∧ ↑((finset.Iio d).bUnion F) ⊆ a.carrier, {
      rw [finset.coe_union] at *,
      rw [set.union_subset_iff] at *,
      assumption
    },

    --FF ⊆ a:
    constructor,
    assumption,

    --((finset.Iio d).bUnion F) ⊆ a:
    rw [finset.coe_bUnion],
    rw [set.Union_subset_iff],
    intro i,
    rw [set.Union_subset_iff],
    intro hi,
    rcases hF i with ⟨P,hP⟩,
    assumption
  },

  --Aus FU ⊆ a folgt sofort ⟨FU⟩ = aa ⊴ a.
  have aa_subset_a : aa.carrier ⊆ a.carrier, {
    suffices : aa ≤ a, {
      assumption
    },
    change ideal.span ↑FU ≤ a,
    rw [ideal.span_le] at *,
    assumption
  },

  --Das Finale:
  have aa_carrier_eq_a_carrier : a.carrier = aa.carrier, {
    --Widerspruchsannahme: a.carrier ≠ aa.carrier.
    by_contra c,

    --Dann existiert ein x ∈ a.carrier ∖ aa.carrier.
    have aa_ssubset_a : aa.carrier ⊂ a.carrier, {
      rw [set.ssubset_iff_subset_ne] at *,
      constructor,
      assumption,
      exact ne_comm.mp c,
    },
    rw [set.ssubset_iff_of_subset aa_subset_a] at aa_ssubset_a,

    let P : R[X] → Prop := λ p, p ∈ a.carrier ∧ p ∉ aa.carrier,
    have C : ∃ g : R[X], P g, {
      rcases aa_ssubset_a with ⟨g,gh⟩,
      use g,
      rcases gh with ⟨g',hg'⟩,
      change g ∈ a.carrier ∧ g ∉ aa.carrier,
      constructor,
      assumption,
      assumption
    },

    --Wähle g ∈ a von minimalem Grad.
    rcases C with ⟨g,hg⟩,
    --wlog h' : ∀ p, P p → g.degree ≤ p.degree,
    have g_min : ∀ p, P p → g.degree ≤ p.degree, {
      sorry --wlog_sorry
    },

    --Sei u ∈ R der Leitkoeffizient von g.
    let u := leading_coeff g,

    --Dann ist u ∈ bb.
    have u_in_bb : u ∈ bb, {
      let d₀ := g.nat_degree,
      have : u ∈ (b d₀), {
        change u ∈ submodule.map (η d₀) (a.degree_le ↑d₀),
        rw [submodule.mem_map],
        use g,
        constructor, {
          change g ∈ a.degree_le ↑g.nat_degree,
          unfold ideal.degree_le,
          constructor, {
            simp,
            rw [polynomial.mem_degree_le],
            simp
          }, {
            simp,
            rw [ideal.mem_of_polynomial g],
            exact and.left hg
          },
        }, {
          change g.leading_coeff = (lcoeff R d₀) g,
          simp
        },
      },

      change u ∈ ⨆ (k : ℕ), b k,
      exact ideal.mem_supr_of_mem d₀ this
    },

    --Mache Fallunterscheidung über den Grad von g.
    by_cases case : g.degree ≥ d, {

      --Sei S = η(d)(FF) eine endliche erzeugende Menge von bb.
      let S := finset.image (η d) FF,
      have S_spans_bb : bb = ideal.span ↑S, {
        change bb = ideal.span (finset.image ⇑(η d) FF),
        rw [hFF₂],
        simp
      },

      --Dann ist u ∈ S.
      have u_in_S : u ∈ submodule.span R ↑S, {
        unfold ideal.span at S_spans_bb,
        rw [S_spans_bb] at u_in_bb,
        assumption
      },

      rw [mem_span_finset] at u_in_S,
      rcases u_in_S with ⟨ρ,hρ⟩,


      --let g₀ := monomial 0 (σ 0) + monomial 1 (σ 1),

      --let g₀ := monomial

      --Dann existieren r_1,...r_n ∈ R mit u = ∑ r_i s_i = ∑ r_i η(f_i).
      --???

      --Konstruiere nun
      --
      --     h₀ : aa := ∑ u_i ⬝ X^{deg(h) - deg(f_i)} ⬝ f_i
      --
      --Dass h₀ ∈ aa ist, sieht man sofort an der Konstruktion (alle f_i sind in aa).

      --have : leading_coeff h = leading_coeff h₀, {
        --Sieht man an der Konstruktion.
        --sorry
      --},

      --have : (h - h₀) ∈ a.carrier ∧ (h - h₀) ∉ aa.carrier, {
        --Wenn (h-h₀) ∈ aa wäre, dann wäre h₀ + (h - h₀) = h ∈ aa.
        --sorry
      --},

      -- Aber dann ist deg(h - h₀) < deg(h), also wurde h nicht minimal gewählt.
      sorry
    }, {
      --Ganz ähnlich.
      sorry,
    },
  },

  --Und schließlich...
  rw [ideal_eq_iff_carrier_eq],
  assumption,

end


