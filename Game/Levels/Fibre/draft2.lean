import Mathlib

example {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (fun x ↦ - f x) := by
  fun_prop

/-- `fun_prop` only knows `Continuous.neg` in the pointwise form `fun x ↦ -(f x)`.
When the goal is stated with the `Pi` negation `-f`, it sees `Neg.neg f x` and gives up,
so we register the same statement in that shape. -/
@[fun_prop]
theorem Continuous.neg' {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [Neg Y] [ContinuousNeg Y] {f : X → Y} (hf : Continuous f) :
    Continuous (fun x ↦ (-f) x) := hf.neg

example {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (-f) := by
  fun_prop
