-- Level name : 1a) Verpackungswahn

import linear_algebra.span

variables {K V W : Type*}

variables [field K]
variables [add_comm_monoid V] [add_comm_monoid W]
variables [module K V] [module K W]
variables M N : set V
variable P : set W
variable f : V →ₗ[K] W

open submodule

/-
If `f` is a function and `M` a subset of its domain, then
`f '' M` or `set.image f M` is the notation for the image, which is
usally denoted `f(M) = {y | ∃ x ∈ M, f(x) = y}` in mathematical texts.
-/

/- Lemma
Beweise.
-/
example : f '' (span K M) = span K (f '' M) :=
begin
  simp,
end
