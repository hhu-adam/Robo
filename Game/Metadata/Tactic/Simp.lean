import Lean.Meta.Tactic.Simp
import Game.Metadata.Tactic.SimpLog

/-- Custom simp set to restrict the player's simp calls. -/
register_simp_attr game_simp

/- `simp` tatics for player -/
macro_rules
  | `(tactic| simp)                          => `(tactic| try simp only [game_simp])
  | `(tactic| simp [$args,*])                => `(tactic| try simp only [game_simp, $args,*])
  | `(tactic| simp $loc:location)            => `(tactic| try simp only [game_simp] $loc:location)
  | `(tactic| simp [$args,*] $loc:location)  => `(tactic| try simp only [game_simp, $args,*] $loc:location)

/- `simp?` versions -- not currently enabled in game -/
macro_rules
  | `(tactic| simp?)                         => `(tactic| try simp? only [game_simp])
  | `(tactic| simp? [$args,*])               => `(tactic| try simp? only [game_simp, $args,*])
  | `(tactic| simp? $loc:location)           => `(tactic| try simp? only [game_simp] $loc:location)
  | `(tactic| simp? [$args,*] $loc:location) => `(tactic| try simp? only [game_simp, $args,*] $loc:location)

/- For authoring:
 * When developing a level, write `simp_log` (defined in `Game.Metadata.Tactic.SimpLog`)
   instead of `simp`. It runs the full simp set and logs every used lemma's fully qualified name
   during `lake build`, so `extract_simp_lemmas.py` can collect them into `simp_list.lean`.
 * for debugging purposes, `simp (config := {})` can be used to circumvent the above macro_rules
   and access the usual `simp`. In particular,
   `simp? (config := {})`  and
   `simp? (config :={}) [game_simp]`
   can be used to compare the lemmas fired by the usual `simp` with those fired after restriction
   to the list `game_simp`.
-/


/-
# Notes on possible further enhancements

There are 3 design decisions involved in defining a custom simp of the game:

  - *static versus dynamic* set of simp lemmas:  Should game_simp be a static list, or should it
    also evolve dynamically like the list of available theorems we discussed above, with more simp
    lemmas being unlocked as the game progresses?
  - *manual versus automated generation of game_simp list*:  Ideally, there would be some tatic
    author_simp that the author of a game can use in proofs, and this tactic would automatically add
    all lemmas  used by simp to the list game_simp.
  - *hidden versus visible* simp lemmas:  Should the lemmas from the list game_simp be displayed as
    part of the inventory or not?

What is currently implemented is **static + manual + hidden**. Note that it would be very confusing
for a player if we implement *dynamic* without also making the currently available simp list
*visible*.
-/
