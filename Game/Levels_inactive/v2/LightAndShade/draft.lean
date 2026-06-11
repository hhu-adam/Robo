import Mathlib

/-
23. Light and Shadow (Shade?). Let f : ℝ → ℝ be a continuous function. A real number s is called a
    shadow point of f if there exists a real number t with t > s and f(t) > f(s). If a and b with a
    < b are themselves not shadow points, but every s between a and b is a shadow point, then f(a) =
    f(b). (Hint: Assume f(a) > f(b). Then one can find an s between a and b with f(s) > f(b). To
    arrive at a contradiction, one can consider the supremum of {t ∈ ]s, b[ | f(t) > f(s)}.)-/

variable (f : ℝ → ℝ )
variable (a b : ℝ)

def Shade : Set ℝ := {s : ℝ | ∃ t > s, f t > f s }

example (hf : Continuous f) (hab : a < b) (ha : a ∉ Shade f) (hb : b ∉ Shade f)
   (h : ∀ k ∈ Set.Ioo a b, k ∈ Shade f) : f a = f b := by
  obtain h | h | h := lt_trichotomy (f a) (f b)
  · have p : a ∈ Shade f
    use b
    contradiction
  · assumption
  · have as1 : ∃ s ∈ Set.Ioo a b, f s > f b := by
      have as2: Set.Ioo (f b) (f a) ⊆ f '' Set.Ioo a b := by
        apply intermediate_value_Ioo'
        linarith
        exact Continuous.continuousOn hf
      have set_not_empty : (Set.Ioo (f b) (f a)).Nonempty := by
          use (f b + f a) / 2
          constructor
          linarith
          linarith
      obtain ⟨z, hz⟩ := set_not_empty
      have hz' := hz
      apply as2 at hz
      simp at hz
      choose zz hzz using hz
      use zz
      constructor
      simp [hzz]
      obtain ⟨h1, h2⟩ := hzz
      simp at hz'
      obtain ⟨hh1, hh2⟩ := hz'
      simp
      rw [← h2] at hh1
      assumption
    obtain ⟨s, hs⟩ := as1
    have as3 : Set ℝ := {t ∈ Set.Ioo s b | f t > f s}
    have kk: Max as3

    done
