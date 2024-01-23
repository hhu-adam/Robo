import data.real.basic
import topology.basic
import tactic 
import data.set.basic
import order.interval
import data.real.sign
/-
Um den zwischenwertsatz zu beweisen, wollen wir erstmal Bolzanos Nullstellensatz
zeigen.
dazu brauchen wir lokale stetigkeit:
dann globale stetigkeit,
dann versuchen wir bolzanos nullstellensatz zu beweisen, d.h. eventuell brauchen wir mehr
dann beweisen wir den zwischenwertssatz.
-/

/-Definiere ein Intervall
 beachte: wenn a>b ist es die leere Menge-/
def I (a:ℝ)(b:ℝ ) : set ℝ := { x:ℝ | a ≤ x ∧  x ≤ b}

/-epsylon delta kriterium für lokale stetigkeit
Sei f : D -> ℝ  eine abb =>
f stetig  in x0 ∈ D <=> ∀ ε>0 ∃δ>0 ∀x∈D : |x0 -x| < δ => |f(a) -f(x0)| <ε 
-/
def lok_stetig_def (x0:ℝ )(f:ℝ  -> ℝ ):Prop:=
∀(ε:ℝ ), ε > 0 ∧  ∃ δ > 0, ∀ (x:ℝ) , |x0 -x| < δ -> |f(x) -f(x0)| <ε 


/-globale stetigkeit <=> lokal stetig auf ganz R-/
def stetig (D:set ℝ ) (f:ℝ -> ℝ ):Prop:=
∀ (x∈D), lok_stetig_def x f

/-Das bild eines Intervalls ist unter einer Stetigen Funtkion wieder ein Intervall-/
/-TODO: das zu einem Satz zu machen, oder zu finden-/
def bild_von_intervall_von_stetiger_fktn (a :ℝ )(b:ℝ )(D: set ℝ :={ x:ℝ | a<x ∧ x < b} )(f: ℝ -> ℝ )(hf: stetig D f):Prop:=
f '' D = I (f a) (f b)

/-Bolzanos Nullstellensatz:
Sei F eine stetige funktion und f(a) < 0 ∧  f(b) > 0 mit a,b ∈ ℝ 
=> ∃ x ∈ [a,b] : f(x) = 0
-/

-- def converges (f : ℕ → ℚ) :=
--   ∀ ε > 0, ∃ N, ∀ m n ≥ N, |f m - f n| < ε

-- -- Definiere den Limit einer Folge irgendwie
-- def limit {f : ℕ → ℚ} (h : converges f) := real.of_cauchy f


noncomputable theory

noncomputable
def bisection (f : ℝ → ℝ) : ℝ → ℝ → ℕ → ℝ × ℝ  
| a b 0 := (a, b)
| a b (n + 1) :=
  let c := (b - a)/2 in
  if (f a).sign = (f c).sign then
    bisection c b n
  else
    bisection a c n

def bisection_folge (f : ℝ → ℝ) (a b : ℝ) : ℕ → ℝ := λ n, (bisection f a b n).1
-- Grenzwerte
-- stetige Funktionen sind mit grenzwerten kompatibel
-- bisection convergiert.



def converges (f : ℕ → ℝ) :=
  ∀ ε > 0, ∃ N, ∀ m n ≥ N, |f m - f n| < ε

-- Definiere den Limit einer Folge irgendwie
lemma limit_exists (f : ℕ → ℝ) (h : converges f) :
  ∃ y, ∀ ε > 0, ∃ N, ∀ n ≥ N, |f n - y| < ε :=
begin
  sorry
end

def limit {f : ℕ → ℝ} (h : converges f) := (limit_exists f h).some

lemma bisection_converges (f : ℝ → ℝ) (a b : ℝ) :
  converges (bisection_folge f a b) := 
begin
  intros ε hε,
  use nat.ceil((b - a)/(2*ε)),
  -- ` (b - a)/(2ε) < log(b - a) / (ε * log(2)) < N`
  -- also `(b -a) / 2^ N < ε`
  intros m hm n hn,
  sorry
end

lemma bisection_limit_in (f : ℝ → ℝ) (a b : ℝ) : (limit (bisection_converges f a b)) ∈ I a b := 
begin
  sorry
end

lemma bisection_limit_eq (f : ℝ → ℝ) (a b : ℝ) : f (limit (bisection_converges f a b)) = 0 :=
begin
  sorry
end

lemma bolzanos_nullstellensatz (D:set ℝ )(a:ℝ  )(b:ℝ  )(f:ℝ -> ℝ )(hf: stetig D f )(ha: a ∈ D)(hb: b∈ D):
f(a) < 0 ∧  f(b) > 0 -> ∃ x ∈ I a b, f(x) = 0 :=
begin
  intro i,
  by_cases  a = b,
 { 
  simp [stetig] at hf,
  simp [lok_stetig_def] at hf, 
  rcases i with ⟨ ga,gb⟩, 
  rewrite[h] at ga,
  exfalso,
  apply lt_asymm ga,
  assumption,
  },

/-
 Beweisstratege:
 schaue, ob der Mittelwert die Nullstelle ist, wenn nein wähle den Mittelwert und die
 grenze intervallgrenze, deren Bild ein anderes vorzeichen, als das Bild vom Mittelwert ist,
 wiederhole vorgehen auf neuem intervall.

 dieser beweis hätte unendliche laufzeit, daher machen wir ihn nicht...
 
  by_cases f ((a+b)/2) = 0,
  {
    use (a+b)/2,
    split,
    /-mittelwert ist im intervall-/
    
    right,

  },
  -/

  /-Beweisstrategie: betrachte das Bild des Intervalls und schaue, ob es die 0 enthält-/

  let k := f '' I a b,
  /-annehmen, dass 0 ∈ k
  definition von k gibt ein x dass das goal erfüllen könnte
  set.mem_image
  -/
  
  unfold I,
  simp [stetig] at hf,
  simp [lok_stetig_def] at hf,
  
  let x := limit (bisection_converges f a b),
  use x,
  constructor,
  apply bisection_limit_in,
  apply bisection_limit_eq,
end
