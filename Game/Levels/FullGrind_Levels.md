# Levels using FullGrind

Criterion: a level counts only if it enables scoped full grind via `open ... FullGrind`.
`Game/Levels/Babylon/Babylon_grind.md` is documentation only and is not counted.

**6** levels use FullGrind:

| World | Level | open statement |
|-------|-------|----------------|
| Babylon | L04 | `open Finset FullGrind` |
| Babylon | L05 | `open Finset Nat FullGrind` |
| Euklid | L02 | `open Finset FullGrind` |
| Samarkand | L06 | `open Function Set FullGrind` |
| Samarkand | L09 | `open Function FullGrind` |

# Levels where the old proof was kept in a `Branch`

These are levels where the main proof was golfed (usually down to `grind`), and the
original ("old") proof was packaged separately inside a `Branch` block, marked with an
`-- old proof` comment.

**8** levels (9 old-proof blocks; Babylon L05 has two):

| World | Level | old proof location |
|-------|-------|--------------------|
| Babylon | L04 | L53 |
| Babylon | L05 | L57, L73 |
| Samarkand | L09 | L34 |
| Mono | L01 | L41 |
| Mono | L04 | L66 |
| Vieta | L04 | L59 |
| Vieta | L06 | L42 |
| Vieta | L10 | L68 |
