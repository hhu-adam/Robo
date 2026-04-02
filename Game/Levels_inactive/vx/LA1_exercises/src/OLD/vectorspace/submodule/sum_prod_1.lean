-- Level name : Interne Summe

/-
Die interne Summe von Untermodulen wird in Lean mit `⊔` (`\sup`) geschrieben.
-/

import linear_algebra.span
open submodule    -- to write `span` instead of `submodule.span`

variables {K V W : Type*} [field K] [add_comm_monoid V] [module K V]
variables (V₁ V₂ : submodule K V)

/- Lemma
Zeige, dass `V₁ ⊔ V₂` tatsächlich die interne Summe `⟨V₁ ∪ V₂⟩` ist.
-/
lemma sup_eq_span_union : V₁ ⊔ V₂ = span K ( (V₁ : set V) ∪ V₂ ) :=
begin
  rw submodule.span_union,
  simp,
end
