
/-
Functions are at the very core of Lean: As a functional programming language
almost everything is internally a function. Therefore
functions connect various things.

We define a function $f : \\mathbb{N} \\to \\mathbb{N}$ in Lean as `(f : ℕ → ℕ)` (`\\to`).
This is a generic function and does not say anything about the values of $f$.




Eine Funktion mit expliziten Werten definiert man folgendermassen:
`fun (x : ℕ) ↦ 2 * x` (`\\mapsto`, oder alternativ `=>`). Man kann diese direkt anonym brauchen, oder man kann diese dann
mit `let` einem Namen zuweisen: `let f := fun (x : ℕ) ↦ 2 * x`.

Eine Funktion, die mehrere Werte nimmt, schreibt man ganz einfach mit `fun (x : ℕ) (y : ℕ) ↦ x + 2 * y`.


Wenn `(f : A → B)` eine Funktion von $A$ nach $B$ ist, und `(x : A)` ein Element in $A$, dann ist `f x` das Bild
in $B$.



Wenn man zeigen will, dass zwei Funktionen gleich sind (`f = g`), kann man `funext i` benutzen. Danach muss man zeigen, dass
`f i = g i` für ein beliebiges `i`.



Zwei Funktionen `f : A → B` und `g : B → C` kann man mit `g ∘ f` (`\\comp`) komponieren.



-- injective/surjective/bijective


## Mengenlehre

-- #check f ⁻¹' ∅ --preimag
-- #check f '' univ
-- #check range f
-- -- #check set.piecewise A f g -- is f on A and g on its complement



## Aufgaben


`fun (x : ℕ) ↦ 2 * x` (`\\mapsto`).

`fun (x : ℕ) (y : ℕ) ↦ x + y`

`if ... then ... else ...`

Erster Teil: über natürlichen Zahlen
- `f(3) = 9`
- `f(x) ≤ f(x+1)`
- `∃ f, f(0) = 0 ∧ ∀ x ≥ 0, g(x) ≤ f(x)`
- `x ↦ x^2` ist injektiv
- `x ↦ x^2` ist nicht surjektiv
- `f(x) ≥ 0` für eine gewisse Funktion... `linarith` einführen.
- Zeige `g ∘ f = id`.




Funktionen 2. Teil, sobald man sets kennt:
- `A, B` sets, `f : A → B` injektiv. Dann existiert `g : B → A` such that `g ∘ f = id`. (schwierig)


-/



#check λ (x:ℕ), ite (x < 0) (x*2) 0
#check λ (x:ℕ), if (x < 0) then (x*2) else 0

#check funext