-- Level name : Exists Unique

import tactic.interactive
import algebra.algebra.basic

/-
Im weiten wird seltener auch `∃!` verwendet, wenn ein Element existiert und eindeutig ist.

`∃ x, (P x) ∧ (∀ y, P y → y = x)`

TODO : This Level has not been created yet. Find a good exercise.
TODO: Should there be another level about `∀` as notation for products/families.
Or probably way too early to do that here?
-/

/- Lemma : no-side-bar
Beweise.
-/
lemma replace_me_please : ∃! x, x = 2 :=
begin
  use 2,
  constructor,
  { simp },
  { intros y hy,
   exact hy },
end
