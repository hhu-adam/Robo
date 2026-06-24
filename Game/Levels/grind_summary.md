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
| Babylon/L04 | `grind` for `Icc 3 n ⊆ Icc 0 n`; case split `i = 0 ∨ i = 1 ∨ i = 2` |
| Babylon/L05 | `grind [Odd.neg_pow]` / `grind [Even.neg_pow]` |
| Babylon/L06 | after `rw [← insert_Icc_right_eq_Icc_add_one]`, then `grind` (uses the induction hypothesis) |
| Babylon/L07 | after `rw [← insert_Icc_left_eq_Icc_sub_one]`, then `grind` (same as L06) |
| Babylon/L08 | after `rw [← insert_Icc_right_eq_Icc_add_one]`, then `grind` (same as L06) |
| Babylon/L09 | after `rw [← insert_Icc_right_eq_Icc_add_one]`, then `grind [arithmetic_sum]` (same as L06) |
| Iso/L02 | after `use g`, then `grind` (avoids manual `constructor`) |
| Euklid/L01 | after `intro`, then `grind [prime_def]` |
| Euklid/L02 | after `rw [prod_insert]`, then `grind` |
| Samarkand/L01 | directly `grind` |
| Samarkand/L02 | directly `grind` |
| Samarkand/L04 | after `obtain ⟨a, ha⟩ := hf b`, then `grind` |
| Samarkand/L07 | directly `grind` |
| Cantor/L01 | `grind` at the two `by_cases` branches (lines 81, 85) |
| Cantor/L03 | after `unfold IsFixedPt`, then `grind` |
| Cantor/L06 | after `unfold IsFixedPt`, then `grind` |
| Cantor/L07 | after `apply congr_fun at h`, then `grind` |
| Cantor/L09 | after `unfold fixedPoints IsFixedPt`, then `grind` |
| Robotswana/L08 | if_neg branch `grind [zero_on_offDiag_ebasis]` needs ematch (if_pos branch alone is fine without it) |
| Robotswana/L09 | `grind [map_sum, eq_on_diag_ebasis]` and `grind [ebasis_diag_sum_eq_one]` |
| Epo/L04 | forward direction by `grind` |
| Epo/L05 | after `use g`, then `grind` |
| Mono/L09 | after `obtain ⟨g, hg⟩ := h`, then `grind` |
| Mono/L10 | first `by_cases` branch closed by `grind` |
| Mono/L11 | after `use g` (fwd) and after `obtain ⟨g, hg⟩ := hL` (bwd), then `grind` |
| Prado/L03 | directly `grind` |
| Prado/L06 | after `obtain ⟨hp₁, hp⟩ := hp`, then `grind` |
| Prado/L10 | after `rw [even_iff_two_dvd] at h; rw [prime_def] at hp`, then `grind` |

---

## Class B — solved by `grind` AND by `grind (ematch := 0)`

| Level | How to close |
|-------|--------------|
| Samarkand/L05 | after `use a`, then `grind` |
| Cantor/L08 | after `unfold IsFixedPt`, then `grind` |
| Mono/L01 | `grind` after `intro a b` |
| Mono/L04 | `grind` after `intro a₁ a₂ h` |
| Mono/L06 | `grind [hf hlt]` and `grind [hf hgt]` |
| Vieta/L04 | after `use fun (x : ℤ) ↦ x - 3`, then `grind` |
| Vieta/L06 | only `grind` needed; works even before `funext` |
| Vieta/L10 | after `apply congr_fun at hs; specialize hs b`, then `grind` |

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
