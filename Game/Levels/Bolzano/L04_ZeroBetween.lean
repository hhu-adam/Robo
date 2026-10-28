import Game.Levels.Bolzano.L03_CrossRight

World "Bolzano"
Level 4

Introduction "Intro Bolzano L04"

open Set FullGrind

/-- If a continuous function is negative somewhere in an open interval and positive somewhere
else in it, then it vanishes at a third point of that interval. -/
TheoremDoc exists_zero_of_neg_of_pos as "exists_zero_of_neg_of_pos" in "Bolzano"

Statement exists_zero_of_neg_of_pos {f : ℝ → ℝ} {a b c d : ℝ} (hf : Continuous f)
    (hc : c ∈ Ioo a b) (hd : d ∈ Ioo a b) (hfc : f c < 0) (hfd : 0 < f d) :
    ∃ e ∈ Ioo a b, f e = 0 := by
  obtain ⟨hc₁, hc₂⟩ := hc
  obtain ⟨hd₁, hd₂⟩ := hd
  have hcases : c ≤ d ∨ d ≤ c := by
    grind
  obtain h | h := hcases
  · have hmem : (0 : ℝ) ∈ f '' Ioo c d := by
      apply intermediate_value_Ioo h _
      · grind
      · fun_prop
    obtain ⟨e, he, hee⟩ := hmem
    obtain ⟨he₁, he₂⟩ := he
    use e
    grind
  · have hmem : (0 : ℝ) ∈ f '' Ioo d c := by
      apply intermediate_value_Ioo' h hf.continuousOn
      constructor <;> grind
    obtain ⟨e, he, hee⟩ := hmem
    obtain ⟨he₁, he₂⟩ := he
    refine ⟨e, ⟨?_, ?_⟩, hee⟩ <;> grind

TheoremTab "Bolzano"
