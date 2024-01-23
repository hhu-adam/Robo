import ring_theory.noetherian
import ring_theory.polynomial.basic

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

  --Für n ∈ ℕ sei b(n) ⊆ R die Menge der Leitkoeffizienten der Polynome f ∈ a mit deg(f) ≤ k.
  --Betrachte dazu die Menge a(n) = {f ∈ a | deg(f) ≤ k} ⊆ a. Dann ist die Abbildung
  --
  --                      η(n) : a(n) → R, f ↦ leading_coeff(f)
  --
  --ein Modulhomomorphismus. Damit ist b(n) := im η(n) ⊴ R insbesondere ein Ideal von R. Die
  --Abbildung η(n) ist bereits implementiert als "polynomial.lcoeff R k".
  let η := lcoeff R,
  let b : ℕ → ideal R := λ n, submodule.map (η n) (a.degree_le ↑n),

  --Als Ideal von R ist jedes b(n) endlich erzeugt. Insbesondere existiert für jedes n ∈ ℕ eine endliche
  --Menge F(n) = {f1,...,fn} ⊆ a von Polynomen, so dass die Leitkoeffizieten dieser Polynome b(n) erzeugen.
  have exists_F : ∀ (n : ℕ), ∃ (F : finset R[X]), ↑F ⊆ a.carrier ∧ (b n) = ideal.span (finset.image (η n) F), {

    --Für jedes n ∈ ℕ besitzt b(n) ein Urbild unter η(n) in a(n).
    have bn_has_preimage : ∀ n : ℕ, ∀ y : R, ∃ x, y ∈ (b n) → x ∈ a.degree_le ↑n ∧ (η n) x = y, {
      intro n,
      intro y,
        by_cases hy : y ∈ b n,
        { rw [submodule.mem_map] at hy,
          rcases hy with ⟨x,hx⟩,
          use x,
          intro,
          assumption,
          },
        { use default,
          }
    },

    --Sei μ : ℕ → R → R[X] eine Rechtsinverse von η(n), das heißt für alle n ∈ ℕ und y ∈ R
    --gilt (η(n) ∘ μ)(y) = y.
    let μ : ℕ → R → R[X] := λ n y, (bn_has_preimage n y).some,
    have hμ : ∀ (n : ℕ), ∀ (y : R), y ∈ (b n) → (μ n y) ∈ (a.degree_le ↑n) ∧ (η n) (μ n y) = y, {
      intro n,
      intro y,
      exact (bn_has_preimage n y).some_spec
    },

    --Sei S eine erzeugende Menge von b(n).
    intro n,
    rcases R_noetherian (b n) with ⟨S,hS⟩,

    --Offenbar gilt S ⊆ b(n).
    have S_subset_bn : ↑S ⊆ (b n).carrier,
    { rw [← hS], apply ideal.subset_span, },

    --Wähle als F(n) nun "einfach" μ(S).
    use S.image (μ n),
    constructor,
    { intros x hx,
      norm_cast at hx,
      rw [finset.mem_image] at hx,
      rcases hx with ⟨y, hy, hxy⟩,
      subst hxy,
      apply (hμ n y (S_subset_bn hy)).1.2, },
    { rw [← hS],
      congr,
      apply subset_antisymm,
      { intros y hy,
        rw finset.mem_image,
        use μ n y,
        constructor,
        apply finset.mem_image_of_mem,
        apply hy,
        exact (hμ n y (S_subset_bn hy)).2, },
      { intros x hx,
        rw finset.mem_image at hx,
        rcases hx with ⟨y, hy, hxy⟩,
        --norm_cast at hy,
        rw [finset.mem_image] at hy,
        subst hxy,
        rcases hy with ⟨x, hx, hxy⟩,
        subst hxy,
        rw (hμ n x (S_subset_bn hx)).2,
        exact hx,
      } },
  },

  let F := λ n, (exists_F n).some,
  have hF : ∀ (n : ℕ), ↑(F n) ⊆ a.carrier ∧ b n = ideal.span (finset.image (η n) (F n)), {
    intro n,
    exact (exists_F n).some_spec
  },

  --Sei B die Vereinigung aller b(n).
  let B : ideal R := ⨆ (n : ℕ), (b n),

  --Als Ideal von R ist auch B eine endlich erzeugt. Es existiert sogar ein N ∈ N, so dass
  --B von dein Leitkoeffizienten der Polynome in F(N) erzeugt wird.
  have exists_N : ∃ (N : ℕ), B = ideal.span (finset.image (η N) (F N)), {

    --Sei S ⊆ B eine erzeugende Menge von B.
    rcases R_noetherian B with ⟨S,hS⟩,
    have S_subset_B : ↑S ⊆ B.carrier, {
      rw [← hS],
      apply ideal.subset_span
    },

    --Dann existiert bereits ein N ∈ ℕ mit S ⊆ b(N).
    have S_subset_bN : ∃ (N : ℕ), ↑S ⊆ (b N).carrier, {
      --S ⊆ ⋃ (n : ℕ), (b n).carrier
      --∀ (s : S), ∃ (n : ℕ), s ∈ (b n)
      --S finite ⇒ ∃ (N : ℕ), ∀ (s : S), s ∈ (b N)
      sorry
    },

    rcases S_subset_bN with ⟨N,hN⟩,

    have B_eq_bk : B = (b N), {
      suffices : B ≤ b N ∧ B ≥ b N, {
        rw [ideal_eq_iff_carrier_eq],
        rw [set.subset.antisymm_iff],
        assumption,
      },
      constructor, {
        rw [←hS],
        rw [ideal.span_le],
        assumption
      }, {
        change b N ≤ ⨆ (n : ℕ), b n,
        simp,
        rw [le_supr_iff],
        intros I hI,
        exact (hI N)
      },
    },

    use N,
    rw [B_eq_bk],
    exact (hF N).right
  },

  --Wähle N minimal.
  rcases exists_N with ⟨N,hN⟩,
  have N_minimal : ∀ (n : ℕ), n < N → B < ideal.span (finset.image (η n) (F n)), {
    sorry --wlog_sorry
  },

  --Konstruiere nun FU = F(0) ∪ F(1) ∪ ... ∪ F(N) ⊆ a(N). Als endliche Vereinigung von
  --endlichen Mengen ist FU endlich. Sei ferner A = ⟨FU⟩ ⊴ R[X] ein endlich erzeugtes Ideal.
  let FU : finset R[X] := finset.bUnion (finset.Iic N) F,
  let A : ideal R[X] := ideal.span ↑FU,

  --Wir zeigen nun, dass a gleich A ist.
  --Daraus folgt die Behauptung.
  suffices : a = A, {
    use FU,
    rw [this] at *
  },

  --Zu erst ein paar Kleinigkeiten.

  --Es gilt F(n) ⊆ a für jedes n ∈ ℕ, also gilt auch FU ⊆ a.
  have FU_subset_a : ↑FU ⊆ a.carrier, {
    change ↑((finset.Iic N).bUnion F) ⊆ a.carrier,
    rw [finset.coe_bUnion],
    rw [set.Union_subset_iff],
    intro i,
    rw [set.Union_subset_iff],
    intro hi,
    rcases hF i with ⟨P,hP⟩,
    assumption
  },

  --Aus FU ⊆ a folgt sofort ⟨FU⟩ = A ⊴ a.
  have A_subset_a : A.carrier ⊆ a.carrier, {
    suffices : A ≤ a, {
      assumption
    },
    change ideal.span ↑FU ≤ a,
    rw [ideal.span_le] at *,
    assumption
  },

  --Das Finale:
  have A_carrier_eq_a_carrier : a.carrier = A.carrier, {
    --Widerspruchsannahme: a.carrier ≠ A.carrier.
    by_contra c,

    --Dann existiert ein x ∈ a.carrier ∖ A.carrier.
    have A_ssubset_a : A.carrier ⊂ a.carrier, {
      rw [set.ssubset_iff_subset_ne] at *,
      constructor,
      assumption,
      exact ne_comm.mp c,
    },
    rw [set.ssubset_iff_of_subset A_subset_a] at A_ssubset_a,

    have C : ∃ g : R[X], g ∈ a.carrier ∧ g ∉ A.carrier, {
      rcases A_ssubset_a with ⟨g,gh⟩,
      use g,
      rcases gh with ⟨g',hg'⟩,
      change g ∈ a.carrier ∧ g ∉ A.carrier,
      constructor,
      assumption,
      assumption
    },

    --Wähle g mit minimalem Grad.
    rcases C with ⟨g,hg⟩,
    have g_minimal : ∀ (f : R[X]), f.degree < g.degree → ¬(f ∈ a.carrier ∧ f ∉ A.carrier), {
      sorry --wlog_sorry
    },

    --Sei u ∈ R der Leitkoeffizient von g.
    let u := leading_coeff g,

    --Dann ist u ∈ B.
    have u_in_B : u ∈ B, {
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

      change u ∈ ⨆ (n : ℕ), b n,
      exact ideal.mem_supr_of_mem d₀ this
    },

    --Mache Fallunterscheidung deg(g).
    by_cases case : g.degree ≥ N, {

      --Schreibe u als Linearkombination der Leitkoeffizienten der Polynome in F(N).
      rw [hN] at u_in_B,
      rw [← ideal.submodule_span_eq] at u_in_B,
      rw [mem_span_finset] at u_in_B,
      rcases u_in_B with ⟨ρ,hρ⟩,

      --no shot

      --let g₀ := monomial 0 (σ 0) + monomial 1 (σ 1),

      --let g₀ := monomial

      --Konstruiere nun
      --
      --     h₀ : A := ∑ u_i ⬝ X^{deg(h) - deg(f_i)} ⬝ f_i
      --
      --Dass h₀ ∈ A ist, sieht man sofort an der Konstruktion (alle f_i sind in A).

      --have : leading_coeff h = leading_coeff h₀, {
        --Sieht man an der Konstruktion.
        --sorry
      --},

      --have : (h - h₀) ∈ a.carrier ∧ (h - h₀) ∉ A.carrier, {
        --Wenn (h-h₀) ∈ A wäre, dann wäre h₀ + (h - h₀) = h ∈ A.
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

