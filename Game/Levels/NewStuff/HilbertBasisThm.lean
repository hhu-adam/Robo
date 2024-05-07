import Game.Metadata

World "TmpHilbertBasis"
Level 1

Title "Hilbert Basis Theorem"

-- TODO: Proof by Marcello

Introduction ""

open Polynomial

variables {R : Type} [CommRing R] [DecidableEq R] [DecidableEq R[X]]


lemma ideal_eq_iff_carrier_eq (a : Ideal R) (b : Ideal R) :
    a = b ↔ a.carrier = b.carrier := by
  constructor
  · intro h
    ext
    Hint "\{{h}}"
    rw [h]
  · intro h
    rw [← Ideal.span_eq a]
    rw [← Ideal.span_eq b]
    change Ideal.span a.carrier = Ideal.span b.carrier
    exact congr_arg Ideal.span h

Statement hilbert_basis_theorem [R_noetherian : IsNoetherianRing R] : IsNoetherianRing R[X] := by
  --Behauptung: Sei R ein noetherscher Ring. Dann ist auch R[X] noethersch.
  --Es reicht zu zeigen: Jedes Ideal a ⊴ R[X] ist endlich erzeugt.
  rw [isNoetherianRing_iff_ideal_fg]
  rw [isNoetherianRing_iff_ideal_fg] at R_noetherian

  unfold Ideal.FG at *

  --Sei a ⊴ R[X] ein Ideal von R[X].
  intro a

  --Für n ∈ ℕ sei b(n) ⊆ R die Menge der Leitkoeffizienten der Polynome f ∈ a mit deg(f) ≤ k.
  --Betrachte dazu die Menge a(n) = {f ∈ a | deg(f) ≤ k} ⊆ a. Dann ist die Abbildung
  --
  --                      η(n) : a(n) → R, f ↦ leading_coeff(f)
  --
  --ein Modulhomomorphismus. Damit ist b(n) := im η(n) ⊴ R insbesondere ein Ideal von R. Die
  --Abbildung η(n) ist bereits implementiert als "polynomial.lcoeff R k".
  let η := lcoeff R
  let b : ℕ → Ideal R := fun n => Submodule.map (η n) (a.degreeLE ↑n)

  --Als Ideal von R ist jedes b(n) endlich erzeugt. Insbesondere existiert für jedes n ∈ ℕ eine endliche
  --Menge F(n) = {f1,...,fn} ⊆ a von Polynomen, so dass die Leitkoeffizieten dieser Polynome b(n) erzeugen.
  have exists_F : ∀ (n : ℕ), ∃ (F : Finset R[X]), ↑F ⊆ a.carrier ∧ (b n) = Ideal.span (Finset.image (η n) F)

  · have bn_has_preimage : ∀ n : ℕ, ∀ y : R, ∃ x, y ∈ (b n) → x ∈ a.degreeLE ↑n ∧ (η n) x = y
    · intro n
      intro y
      by_cases hy : y ∈ b n
      · rw [Submodule.mem_map] at hy
        rcases hy with ⟨x,hx⟩
        use x
        intro
        assumption
      · use default
        intro z
        constructor
        exact (hy z).elim
        exact (hy z).elim

    --Sei μ : ℕ → R → R[X] eine Rechtsinverse von η(n), das heißt für alle n ∈ ℕ und y ∈ R
    --gilt (η(n) ∘ μ)(y) = y.
    let μ : ℕ → R → R[X] := fun n y => (bn_has_preimage n y).choose
    have hμ : ∀ (n : ℕ), ∀ (y : R), y ∈ (b n) → (μ n y) ∈ (a.degreeLE ↑n) ∧ (η n) (μ n y) = y
    · intro n
      intro y
      exact (bn_has_preimage n y).choose_spec

    --Sei S eine erzeugende Menge von b(n).
    intro n
    rcases R_noetherian (b n) with ⟨S,hS⟩

    --Offenbar gilt S ⊆ b(n).
    have S_subset_bn : ↑S ⊆ (b n).carrier
    · rw [← hS]
      apply Ideal.subset_span

    --Wähle als F(n) nun "einfach" μ(S).
    use S.image (μ n)
    constructor
    · intros x hx
      norm_cast at hx
      rw [Finset.mem_image] at hx
      rcases hx with ⟨y, hy, hxy⟩
      subst hxy
      apply (hμ n y (S_subset_bn hy)).1.2
    · rw [← hS]
      congr
      apply subset_antisymm
      · intros y hy
        rw [Finset.coe_image, Set.mem_image]
        use μ n y
        constructor
        apply Finset.mem_image_of_mem
        apply hy
        exact (hμ n y (S_subset_bn hy)).2
      · intros x hx
        rw [Finset.coe_image, Set.mem_image] at hx
        rcases hx with ⟨y, hy, hxy⟩
        --norm_cast at hy
        rw [Finset.coe_image, Set.mem_image] at hy
        subst hxy
        rcases hy with ⟨x, hx, hxy⟩
        subst hxy
        rw [(hμ n x (S_subset_bn hx)).2]
        exact hx


  let F := fun n => (exists_F n).choose
  have hF : ∀ (n : ℕ), ↑(F n) ⊆ a.carrier ∧ b n = Ideal.span (Finset.image (η n) (F n))
  · intro n
    exact (exists_F n).choose_spec

  --Sei B die Vereinigung aller b(n).
  let B : Ideal R := ⨆ (n : ℕ), (b n)

  --Als Ideal von R ist auch B eine endlich erzeugt. Es existiert sogar ein N ∈ N, so dass
  --B von dein Leitkoeffizienten der Polynome in F(N) erzeugt wird.
  have exists_N : ∃ (N : ℕ), B = Ideal.span (Finset.image (η N) (F N))
  · --Sei S ⊆ B eine erzeugende Menge von B.
    rcases R_noetherian B with ⟨S,hS⟩
    have S_subset_B : ↑S ⊆ B.carrier
    · rw [← hS]
      apply Ideal.subset_span

    --Dann existiert bereits ein N ∈ ℕ mit S ⊆ b(N).
    have S_subset_bN : ∃ (N : ℕ), ↑S ⊆ (b N).carrier
    · sorry
      --S ⊆ ⋃ (n : ℕ), (b n).carrier
      --∀ (s : S), ∃ (n : ℕ), s ∈ (b n)
      --S finite ⇒ ∃ (N : ℕ), ∀ (s : S), s ∈ (b N)


    rcases S_subset_bN with ⟨N,hN⟩

    have B_eq_bk : B = (b N)
    · suffices : B ≤ b N ∧ B ≥ b N
      · rw [ideal_eq_iff_carrier_eq]
        rw [Set.Subset.antisymm_iff]
        assumption
      constructor
      · rw [←hS]
        rw [Ideal.span_le]
        assumption
      · change b N ≤ ⨆ (n : ℕ), b n
        rw [le_iSup_iff]
        intros I hI
        exact (hI N)

    use N
    rw [B_eq_bk]
    exact (hF N).right

  --Wähle N minimal.
  rcases exists_N with ⟨N, hN⟩
  have N_minimal : ∀ (n : ℕ), n < N → B < Ideal.span (Finset.image (η n) (F n))
  · sorry

  --Konstruiere nun FU = F(0) ∪ F(1) ∪ ... ∪ F(N) ⊆ a(N). Als endliche Vereinigung von
  --endlichen Mengen ist FU endlich. Sei ferner A = ⟨FU⟩ ⊴ R[X] ein endlich erzeugtes Ideal.
  let FU : Finset R[X] := Finset.biUnion (Finset.Iic N) F
  let A : Ideal R[X] := Ideal.span ↑FU

  --Wir zeigen nun, dass a gleich A ist.
  --Daraus folgt die Behauptung.
  suffices : a = A
  · use FU
    rw [this] at *

  --Zu erst ein paar Kleinigkeiten.

  --Es gilt F(n) ⊆ a für jedes n ∈ ℕ, also gilt auch FU ⊆ a.
  have FU_subset_a : ↑FU ⊆ a.carrier
  · change ↑((Finset.Iic N).biUnion F) ⊆ a.carrier
    rw [Finset.coe_biUnion]
    rw [Set.iUnion_subset_iff]
    intro i
    rw [Set.iUnion_subset_iff]
    intro hi
    rcases hF i with ⟨P,hP⟩
    assumption

  --Aus FU ⊆ a folgt sofort ⟨FU⟩ = A ⊴ a.
  have A_subset_a : A.carrier ⊆ a.carrier
  · suffices : A ≤ a
    · assumption
    change Ideal.span ↑FU ≤ a
    rw [Ideal.span_le] at *
    assumption

  --Das Finale:
  have A_carrier_eq_a_carrier : a.carrier = A.carrier
  · --Widerspruchsannahme: a.carrier ≠ A.carrier.
    by_contra c

    --Dann existiert ein x ∈ a.carrier ∖ A.carrier.
    have A_ssubset_a : A.carrier ⊂ a.carrier
    · rw [Set.ssubset_iff_subset_ne] at *
      constructor
      assumption
      exact ne_comm.mp c
    rw [Set.ssubset_iff_of_subset A_subset_a] at A_ssubset_a

    have C : ∃ g : R[X], g ∈ a.carrier ∧ g ∉ A.carrier
    · rcases A_ssubset_a with ⟨g,gh⟩
      use g
      -- rcases gh with ⟨g',hg'⟩
      -- change g ∈ a.carrier ∧ g ∉ A.carrier
      -- constructor
      -- assumption
      -- assumption


    --Wähle g mit minimalem Grad.
    rcases C with ⟨g,hg⟩
    have g_minimal : ∀ (f : R[X]), f.degree < g.degree → ¬(f ∈ a.carrier ∧ f ∉ A.carrier)
    · sorry --wlog_sorry

    --Sei u ∈ R der Leitkoeffizient von g.
    let u := leadingCoeff g

    --Dann ist u ∈ B.
    have u_in_B : u ∈ B
    · let d₀ := g.natDegree
      have : u ∈ (b d₀)
      · change u ∈ Submodule.map (η d₀) (a.degreeLE ↑d₀)
        rw [Submodule.mem_map]
        use g
        constructor
        · change g ∈ a.degreeLE ↑g.natDegree
          unfold Ideal.degreeLE
          constructor
          · simp
            rw [Polynomial.mem_degreeLE]
            simp
          · simp
            rw [Ideal.mem_ofPolynomial g]
            exact And.left hg
        · change g.leadingCoeff = (lcoeff R d₀) g
          simp
          sorry

      change u ∈ ⨆ (n : ℕ), b n
      exact Ideal.mem_iSup_of_mem d₀ this

    --Mache Fallunterscheidung deg(g).
    by_cases case : g.degree ≥ N
    · --Schreibe u als Linearkombination der Leitkoeffizienten der Polynome in F(N).
      rw [hN] at u_in_B
      rw [← Ideal.submodule_span_eq] at u_in_B
      rw [mem_span_finset] at u_in_B
      rcases u_in_B with ⟨ρ,hρ⟩

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
      --Ganz ähnlich.
    · sorry

  --Und schließlich...
  rw [ideal_eq_iff_carrier_eq]
  assumption
  done
