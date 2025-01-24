import tactic.tfae

variables {A B C D E : Prop}

lemma mytfae (h₁ : A → B) (h₂ : B → C) (h₃ : C → D) (h₄ : D → E) (h₅ : E → A) :
  tfae [A, B, C, D, E] :=
begin
  -- tfae_have : 1 → 2,
  -- { exact h₁ },
  -- tfae_have : 2 → 3,
  -- { exact h₂ },
  -- tfae_have : 4 ← 3,
  -- { exact h₃ },
  -- tfae_have : 4 → 5,
  -- { exact h₄ },
  -- tfae_have : 5 → 1,
  -- { exact h₅ },
  tfae_finish,
end

example (h₁ : A → B) (h₂ : B → C) (h₃ : C → D) (h₄ : D → E) (h₅ : E → A) :
  A ↔ B :=
(mytfae h₁ h₂ h₃ h₄ h₅).out 0 1
