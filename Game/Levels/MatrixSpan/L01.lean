import Game.Metadata

World "Span"
Level 1

Title "Scaling Vectors"

Introduction "Welcome to *Span*.

The mathematical stage for this world is a **module**. Let $R$ be a ring. An $R$-module $M$ is
a set equipped with addition and scalar multiplication by $R$, satisfying some compatibility
conditions. In particular, if $R$ is a field, then a module is just a *vector space*.

The notation for scalar multiplication is `•`, which is written `\\smul`.
Scaling interacts with addition exactly the way you would hope: it distributes over sums in
two ways.

In this level you will combine these to simplify a linear combination.
"

open Real Function Set Finset

/-- `smul_add` : for a scalar `a : R` and vectors `x y : M` in any `R`-module `M`, scalar
multiplication distributes over a sum of vectors, i.e. `a • (x + y) = a • x + a • y`. -/
TheoremDoc smul_add as "smul_add" in "LinearAlgebra"

/-- `add_smul` : for scalars `a b : R` and a vector `x : M` in any `R`-module `M`, scalar
multiplication distributes over a sum of scalars, i.e. `(a + b) • x = a • x + b • x`. -/
TheoremDoc add_smul as "add_smul" in "LinearAlgebra"

/-- `one_smul` : for a vector `x : M` in any `R`-module `M`, scaling by the ring's identity `1 : R`
leaves it unchanged, i.e. `(1 : R) • x = x`. -/
TheoremDoc one_smul as "one_smul" in "LinearAlgebra"

Statement {R M : Type*} [CommRing R] [AddCommMonoid M] [Module R M] (x y : M) :
    (2 : R) • x + (-1 : R) • (x + y) = x + (-1 : R) • y := by
  Hint "Distribute the scalar `-1` over the sum `x + y` with `rw [smul_add]`."
  rw [smul_add]
  rw [← add_assoc]
  rw [← add_smul]
  ring
  rw [one_smul]


NewTheorem smul_add add_smul one_smul

TheoremTab "LinearAlgebra"
