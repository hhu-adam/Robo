-- Level name : Ganze Zahlen

import data.int.basic

/-
todo.
-/

/- Lemma : no-side-bar
Beweise.
-/
example (a b : ℤ) : a - b + b = a :=
begin
  exact sub_add_cancel a b,
end
