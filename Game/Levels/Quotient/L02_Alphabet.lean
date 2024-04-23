import Game.Metadata
import Game.Metadata.StructInstWithHoles

World "Quotient"
Level 2

Title "Alphabet"

Introduction
"
Given a setoid structure `s` on `A` and an element `a : A` the equivalence class of `a`
is the set of all elements of `A` that are congruent to `a`, namely `{x : A | s.Rel x a}`.

The function `hole : A → Fin 3` counts the number of holes in the letters of the alphabet.

In this level you will show that

A partition of the finite set alphabet := {A, B, C, …, Z} into the subsets {C, E, F, G, …}, {A, D, O, …} and {B}, and to construct from this a map alphabet → {0,1,2} which has these subsets as fibres? (The map is given by rank H_0, but that's irrelevant for the question.)

"

open Function Set Setoid


inductive Alphabet where
  | A | B | C | D | E | F | G | H | I | J | K | L | M | N | O | P | Q | R | S | T | U | V | W | X | Y | Z

namespace Alphabet

def hole : Alphabet → Fin 3
  | B => 2
  | A => 1
  | D => 1
  | O => 1
  | P => 1
  | Q => 1
  | R => 1
  | _ => 0

lemma hole_eq (x : Alphabet) : hole x = 0 ∨ hole x = 1 ∨ hole x = 2 := by
  cases x
  iterate tauto

/-- A direct proof that `hole ⁻¹' {i}` forms a parition of Alphabet. -/
lemma hole_parition (x : Alphabet) :
    IsPartition {S | ∃ i, S = (hole ⁻¹' {i})} := by
  unfold IsPartition
  constructor
  · intro h
    simp at h
    rcases h with ⟨i, hi⟩
    cases i
    sorry
  · intro a
    use hole ⁻¹' {hole a}
    constructor
    · simp only [mem_setOf_eq]
      simp only [mem_preimage]
      simp only [mem_singleton_iff]
      simp only [exists_unique_iff_exists]
      simp only [exists_prop]
      constructor
      · use hole a
      · tauto
    · intro T
      intro h
      aesop

/- A direct proof that `hole ⁻¹' {i}` forms a parition of Alphabet by using the fact that `hole ⁻¹' {i}` are equivalence classes of `ker hole`.
-/

Statement class_iff_fibre {S : Set Alphabet} : S ∈ (ker hole).classes ↔  ∃ i, S = hole ⁻¹' ({hole i}) := by
  constructor
  · intro h
    simp_rw [classes, mem_setOf] at h
    obtain ⟨y, hy⟩ := h
    use y
    ext
    Branch
      simp only [mem_setOf_eq, mem_preimage, mem_singleton_iff]
      simp [hy]
      simp [ker_def]
    simp [hy]
    simp [ker_def]
  · sorry


lemma hole_parition' (x : Alphabet) :
    IsPartition {S | ∃ i, S = (hole ⁻¹' {i})} := by
  rw [class_iff_fibre]
  apply isPartition_classes



Statement (s : Set Alphabet) : s ∈ (ker hole).classes ↔
    s = {A, D, O, P, Q, R} ∨ s = {B} ∨ s = {C, E, F, G, H, I, J, K, L, M, N, S, T, U, V, W, X, Y, Z} := by
  constructor
  · intro hs
    simp_rw [classes, mem_setOf] at hs
    rcases hs with ⟨y, hy⟩
    sorry


  · sorry

end Alphabet
