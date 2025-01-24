import topology.basic
import topology.path_connected
import analysis.normed_space.basic
import data.set.basic
import algebraic_topology.fundamental_groupoid.simply_connected
import s01
import s02
import s03

/-
# Einfach-zusammenhängende Räume
Wir möchten nun den Begriff der __einfach-zusammenhängenden__ Räume einführen.
Ein einfach-zusammenhängender topologischer Raum ist ein topologischer Raum,
der wegzusammenhängend ist und in dem jede geschlossene Kurve nullhomotop ist.

Hier ist ein Beispiel:
![Beispiel eines einfach-zusammenhängenden Raums](https://en.wikipedia.org/wiki/Simply_connected_space#/media/File:Runge_theorem.svg)
-/

variables {X : Type*} [topological_space X] {x y z : X}

def loops (x : X) : set (path x x) := {γ | γ 0 = x ∧ γ 1 = x}

-- definieren, wann Pfade homotop sind
def is_homotopic_to (γ₁ γ₂ : path x y) : Prop :=
  ∃ (f : path x y → path x y), continuous f ∧ f γ₁ = γ₂

def is_simply_connected (U : set X) [topological_space U] : Prop :=
  is_path_connected U ∧ ∀ (γ : path x x), γ ∈ loops x → is_homotopic_to γ (path.refl x)


/-
Diese Definition ist recht einleuchtend.
In Lean's Mathlib-Bibliothek gibt es eine äquivalente Definition,
welche etwas allgemeiner/abstrakter ist:
-/

#check simply_connected_space
#check simply_connected_def