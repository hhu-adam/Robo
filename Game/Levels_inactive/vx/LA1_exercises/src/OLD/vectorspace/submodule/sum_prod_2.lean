-- Level name : Interne Summe

-- begin hide
import OLD.vectorspace.submodule.sum_prod_1
open submodule
-- end hide

variables {K V W : Type*} [field K] [add_comm_monoid V] [module K V]

/-
Eine interne Summe über eine Familie von Untermodulen `(T : ι → submodule K V)`
wird als `⨆ (i : ι), T i` geschrieben (`\supr`).
-/

variables {ι : Type*} (T : ι → submodule K V)

/- Lemma
-/
lemma supr_eq_span_Union  :
  (⨆ (i : ι), T i) = span K ( ⋃ i, T i) :=
begin
  rw submodule.span_Union,
  simp, --simp_rw [span_eq],
end