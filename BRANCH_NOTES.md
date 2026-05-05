To do:
- [X] set up macro for `simp at *`
- [X] search for "true_simp" in Game.pot, to find unwanted mention of true_simp in Hints.
- [ ] possible change everything back from true_simp to simp, and import Metadata/Tactic/simp.lean only
  in levels where this is need (but might be many in future)

# game_simp migration status (2026-05-05)

## Goal
Replace `true_simp?` with `simp` in level files, after extracting from the build
output which Mathlib lemmas each `true_simp?` actually used and tagging them
`@[game_simp]` with an `attribute [game_simp] ...` line above `Statement`.

## Done
- All level files reachable from the active build (67 files with `Try this:`
  output) have an `attribute [game_simp] ...` line and have `true_simp?`
  replaced with `simp`, except the Robotswana files listed below.
- `Game/Metadata/Tactic/Simp.lean` defines the player-side `simp` macros
  (with `try simp only [game_simp]` to prevent macro fallback) and the
  author-side `true_simp?` (uses `simp? (config := {})` to bypass the macros).

## Outstanding
Four files still contain `true_simp?` because the file-level `attribute
[game_simp]` is too coarse — at certain call sites, the broader simp set
fires extra rewrites that break a later step:

- `Game/Levels/Robotswana/L05_EBasisDiagSum.lean`
- `Game/Levels/Robotswana/L07_EBasisZeroOffDiag.lean`
- `Game/Levels/Robotswana/L08_EvalOnEBasis.lean`
- `Game/Levels/Robotswana/L10_Characterize.lean`

Three approaches to fix individually (in order of UX preservation):
1. Replace problem call site with `simp only [explicit list]` (matches the
   original `Try this:` suggestion). Player sees lemma names at that spot only.
2. Trim the file's `attribute` line and inline the conflicting lemmas as
   `simp [extra]` at the calls that need them.
3. Restructure the proof so it works under the broader simp set.

## Per-file workflow for future migrations
If a new level adds `true_simp?` calls, run `lake build`, then:

```
python3 migrate_simp_in_file.py Game/Levels/Foo/L01.lean
```

The script reads `/tmp/lake-build.log` (or the path given via `--log`),
extracts the suggestions for that one file, inserts/updates the
`attribute [game_simp] ...` line, and replaces `true_simp?` with `simp`.
After it runs, build again — for any `Unknown constant` errors at the
attribute line, re-run the script with `--prune` to drop bad names.

## Files unchanged on purpose
The 16 files containing `true_simp?` that did *not* appear in the build
output (overview.lean, O*.lean, XX_*.lean, sketch_*.lean, etc.) are obsolete
level files not used by the active build. They were intentionally not touched.
