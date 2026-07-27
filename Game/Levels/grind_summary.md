# `grind` Golf Summary

This document collects all levels (across the `*_grind.md` notes) whose goals can be
closed **directly by `grind`** (possibly after a small preparatory step such as `intro`,
`rw`, `unfold`, `use`, or `obtain`).

The levels are split into two classes:

- **Class A — `grind` works, but `grind (ematch := 0)` does NOT.**
- **Class B — `grind` works, and `grind (ematch := 0)` ALSO works.**

<!-- Every entry below has been **verified** by compiling the level with `lake env lean`:

- Entries marked **(recorded)** were already noted in the original `*_grind.md` files.
- Entries marked **(tested)** had no `(ematch := 0)` note; I reconstructed the golfed proof
  and built it with `grind (ematch := 0)`. When that failed I also re-ran it with plain
  `grind` to confirm the reconstruction was valid. All Lean files were reverted afterwards. -->

---

## Class A — solved by `grind`, NOT by `grind (ematch := 0)`

| Level | How to close |
|-------|--------------|
| Babylon/L04 | `grind` for `Icc 3 n ⊆ Icc 0 n` (L52); case split `i = 0 ∨ i = 1 ∨ i = 2` (`grind` at L98) |
| Babylon/L05 | `grind [Odd.neg_pow]` (L56) / `grind [Even.neg_pow]` (L70) |
| Babylon/L06 | after `rw [← insert_Icc_right_eq_Icc_add_one]` (L69), then `grind` (uses the induction hypothesis) |
| Babylon/L07 | after `rw [← insert_Icc_left_eq_Icc_sub_one]` (L56), then `grind` (same as L06) |
| Babylon/L08 | after `rw [← insert_Icc_right_eq_Icc_add_one]` (L35), then `grind` (same as L06) |
| Babylon/L09 | after `rw [← insert_Icc_right_eq_Icc_add_one]` (L29), then `grind [arithmetic_sum]` (same as L06) |
| Iso/L02 | after `use g` (L63), then `grind` (avoids manual `constructor`) |
| Euklid/L01 | after `intro` (L26), then `grind [prime_def]` (L27) |
| Euklid/L02 | after `rw [prod_insert]` (L51), then `grind` |
| Samarkand/L01 | directly `grind` (proof body from L68) |
| Samarkand/L02 | directly `grind` (proof body from L42) |
| Samarkand/L04 | after `obtain ⟨a, ha⟩ := hf b` (L45), then `grind` |
| Samarkand/L07 | directly `grind` (proof body from L24) |
| Cantor/L01 | `grind` at the two `by_cases` branches (L81, L85) |
| Cantor/L03 | after `unfold IsFixedPt` (L49), then `grind` |
| Cantor/L06 | after `unfold IsFixedPt` (L35), then `grind` |
| Cantor/L07 | after `apply congr_fun at h` (L44), then `grind` |
| Cantor/L09 | after `unfold fixedPoints IsFixedPt` (L75), then `grind` |
| Robotswana/L08 | if_neg branch `grind [zero_on_offDiag_ebasis]` (replaces `rw [if_neg h₂]` at L139) needs ematch (if_pos branch at L132 is fine without it) |
| Robotswana/L09 | `grind [map_sum, eq_on_diag_ebasis]` (L176) and `grind [ebasis_diag_sum_eq_one]` (L190) |
| Epo/L04 | forward direction by `grind` (L30) |
| Epo/L05 | after `use g` (L27), then `grind` |
| Mono/L09 | after `obtain ⟨g, hg⟩ := h` (L24), then `grind` |
| Mono/L10 | first `by_cases` branch (L38) closed by `grind` |
| Mono/L11 | after `use g` (L68, fwd) and after `obtain ⟨g, hg⟩ := hL` (L88, bwd), then `grind` |
| Prado/L03 | directly `grind` (proof body from L22) |
| Prado/L06 | after `obtain ⟨hp₁, hp⟩ := hp` (L34), then `grind` |
| Prado/L10 | after `rw [even_iff_two_dvd] at h` (L32) and `rw [prime_def] at hp` (L33), then `grind` |

---

## Class B — solved by `grind` AND by `grind (ematch := 0)`

| Level | How to close |
|-------|--------------|
| Samarkand/L05 | after `use a` (L35), then `grind` |
| Cantor/L08 | after `unfold IsFixedPt` (L64), then `grind` |
| Mono/L01 | `grind` (L40) after `intro a b` (L37) |
| Mono/L04 | `grind` after `intro a₁ a₂ h` (L60) |
| Mono/L06 | `grind [hf hlt]` (L32) and `grind [hf hgt]` (L38) |
| Vieta/L04 | after `use fun (x : ℤ) ↦ x - 3` (L57), then `grind` |
| Vieta/L06 | only `grind` needed; works even before `funext` (L42) |
| Vieta/L10 | after `apply congr_fun at hs` (L65) and `specialize hs b` (L66), then `grind` |

<!-- ---

## Excluded (not a `grind` closure)

These appeared in the notes but are not `grind`-based solutions:

- Robotswana/L03 — replace `tauto` by `rfl`.
- Samarkand/L08 — existing (non-`grind`) solution already in place.
- Mono/L02, Vieta/L05 — problem statement reworked to avoid `grind` closing the goal.

--- -->
<!--
## Testing notes

- Tested by editing the level proof in place, running `lake env lean <file>`, then
  `git checkout` to revert. Toolchain: `leanprover/lean4:v4.30.0-rc2`.
- Mono/L11's first branch uses a `by_cases` that only elaborates inside the game server
  (it needs the game's classical setup); under plain `lean` it errors with
  "Unknown identifier `hb`". I replaced it with
  `rcases Classical.em (…) with hb | hb` purely to test the `grind` calls, then reverted.
- Six levels were reclassified from the previous draft after testing: **Samarkand/L05,
  Mono/L01, Mono/L04, Mono/L06, Vieta/L04, Vieta/L10** all turned out to be Class B
  (`grind (ematch := 0)` succeeds). -->
