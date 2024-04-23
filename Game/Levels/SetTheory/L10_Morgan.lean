import Game.Metadata
import Game.Levels.SetTheory.L09_Complement


World "SetTheory"
Level 10

Title "Morgansche Regeln"

Introduction
"
**Verkäufer**: Haben Sie schon von Morgan gehört? Der hatte letztig dieses ungelöste Problem!
"

open Set

#check compl_union
#check compl_inter
#check mem_compl_iff

Statement
    (A B C : Set ℕ) : (A \ B)ᶜ ∩ (C \ B)ᶜ = ((univ \ A) \ C) ∪ (univ \ Bᶜ) := by
  Hint "**Robo**: Oh du lieber Schaltkreis. Hier ist sind noch mehr aus meinem Speicher."
  rw [←compl_union]
  rw [←union_diff_distrib]
  rw [diff_diff]
  simp_rw [←compl_eq_univ_diff]
  rw [←compl_inter]
  rw [diff_eq_compl_inter]
  rw [inter_comm]

OnlyTactic rw simp_rw tauto trivial assumption rfl «have» «suffices»
-- NewTactic simp_rw
TheoremTab "Set"
NewTheorem Set.mem_compl_iff Set.compl_union Set.diff_diff Set.compl_inter
  Set.diff_eq_compl_inter Set.inter_comm Set.compl_eq_univ_diff
