import Game.Metadata


World "FunctionSurj"
Level 12

Title "Every surjection has a right inverse"


Introduction
"
The preimage of set `S` under a function `f`, denoted by `f ⁻¹' S` is the set of all elements
`x` in the domain of `f` such that `f x` is in `S`.

```
f ⁻¹' S = {x | f x ∈ S}
```

`HasRightInverse.surjective`

"

open Function Set

Statement Surjective.tfae (f : A → B) :
    List.TFAE [Surjective f, ∀ b : B, Set.Nonempty (f ⁻¹' { b }), HasRightInverse f] := by
  tfae_have 1 → 2
  · intro h b
    apply h
  tfae_have 2 → 3
  . intro h
    Branch
      use fun b ↦ (h b).choose
      intro b
      simp
      exact (h b).choose_spec
    choose g hg using h
    use g
    assumption
  tfae_have 3 → 1
  . Branch
      apply HasRightInverse.surjective
    intro ⟨g, inv⟩
    intro b
    use g b
    apply inv
  tfae_finish

section
variable {f : A → B}
#check (Surjective.tfae f).out 1 2
end

NewTheorem Function.HasRightInverse.surjective
TheoremTab "Function"
NewHiddenTactic tfae_have tfae_finish
