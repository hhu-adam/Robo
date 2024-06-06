import Mathlib.Data.Matrix.Notation

/-!
# Matrix Notation delaborator

Used to display Matrix Notation correctly in the infoview

# Issues

* also displays `![![1, 2], [3, 4]]` as `!![1, 2; 3, 4]` even though the `Matrix.of` is missing.
* does not work for `!![]`, `!![,,,]`, `!![;;;]` (i.e. any zero-dim matrices)
-/

open Lean PrettyPrinter Delaborator SubExpr

namespace Matrix

-- RP'd to mathlib: #85107
/-- Short notation for `n x m`-Matrices. -/
notation (name := concreteMatrix) "Mat["n","m"]["R"]" => Matrix (Fin n) (Fin m) R

/-- Unexpander for the notation `![![x, y, …], ![z, w, …], …]`.

Note that `!![x, y, …; z, w, …; …]` expands to `Matrix.of ![![x, y, …], ![z, w, …], …]`,
but since `of` is an equivalence, not a function, the delaborator is for `DFunlike.coe`
instead. And I didn't manage to have `matrixNotationUnexpander` only applied in said -/
@[scoped app_unexpander vecCons]
def matrixNotationUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ ![$term, $terms₁,*] ![]) => `(!![$term, $terms₁,*])
  | `($_ ![$term] ![]) => `(!![$term])
  | `($_ ![$terms₁,*] !![$[$terms₂,*];*]) => `(!![$terms₁,*;$[$terms₂,*];*])
  | _ => throw ()

@[scoped delab app.DFunLike.coe] def delabMatrixOf : Delab :=
  whenPPOption getPPNotation <| withOverApp 6 do
    let #[_, _, _, _, of, M] := (← getExpr).getAppArgs | failure
    if of.isAppOfArity ``Matrix.of 3 then
      if M.isAppOfArity ``vecCons 4 then
        withAppArg do
          let #[α, _, _, _] := (← getExpr).getAppArgs | failure
          -- Only proceed if the vector has again vectors as element,
          -- i.e. if `α` is of the form `Fin n → _`
          match α with
          | .forallE _ (.app (.const `Fin _) _) _ _ =>
            -- TODO:a bit hacky. We just drop the `of`-part and then
            -- the unexpander above will turn the remaining vector into a matrix-notation.
            let body ← delab
            `(term| $body)
          | _ => failure
      else failure
    else failure

end Matrix
