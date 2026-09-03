import Game.Metadata
import Game.Levels.Uncountable.L07

World "Uncountable"
Level 8

Introduction "Intro Uncountable L08"

open Cardinal

Statement : (ℵ₀ : Cardinal.{0}) < ℵ₀ ^ ℵ₀ := by
  Hint "[Hint u8bgf]
  How many maps are there from `β` to `α`? To build one you pick a value in `α` for each of
  the `#β` elements of `β`, independently — one factor `#α` per element of `β`.

  Therefore, the exponentiation of cardinals is *defined* to be
  $$
  \\#\\alpha ^ \\#\\beta = \\#(\\beta \\to \\alpha).
  $$
  "
  Hint "[Hint pwrx] The right hand side counts the maps `ℕ → ℕ`: rewrite `ℵ₀` as `#ℕ`
    and use `Cardinal.power_def`."
  have h : ℵ₀ ^ ℵ₀ = #(ℕ → ℕ) := by
    rw [← Cardinal.mk_nat]
    apply Cardinal.power_def
  rw [h]
  Hint (hidden := true) "[Hint jsvq] A type is uncountable exactly if its cardinality
    exceeds `ℵ₀` — that is `Cardinal.aleph0_lt_mk_iff`. The uncountability itself you
    proved in the previous level."
  rw [Cardinal.aleph0_lt_mk_iff]
  apply nat_seq_uncountable

/---/
TheoremDoc Cardinal.power_def as "Cardinal.power_def" in "Cardinal"

/---/
TheoremDoc Cardinal.aleph0_lt_mk_iff as "Cardinal.aleph0_lt_mk_iff" in "Cardinal"

NewTheorem Cardinal.power_def Cardinal.aleph0_lt_mk_iff
