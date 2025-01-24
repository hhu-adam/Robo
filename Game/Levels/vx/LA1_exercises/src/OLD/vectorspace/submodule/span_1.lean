-- Level name : 1a) Verpackungswahn

import algebra.algebra.bilinear

variables {K V : Type*}
variable M : set V

variables [field K] [add_comm_monoid V] [module K V]

open submodule

/- Lemma
Beweise.
-/
example : span K ↑(span K M) = span K M :=
begin
  exact (span K M).span_eq,
end