import topology.basic
import topology.path_connected
import topology.metric_space.basic
import analysis.inner_product_space.basic
import analysis.normed_space.basic
import data.set.basic
import algebraic_topology.fundamental_groupoid.simply_connected
import data.real.basic
import analysis.special_functions.trigonometric.basic
import s01
import s02
import s03
import s04

/-
# Beweis der Theoreme

## $S^2$ ist einfach-zusammenhängend

Wir wollen zeigen, dass $S^2$ einfach-zusammenhängend ist.
Dazu zeigen wir, dass jede geschlossene Kurve in $S^2$ nullhomotop ist.
Sei $f: S^1 \to S^2$ eine geschlossene Kurve in $S^2$.
Wir definieren eine Homotopie $H: S^1 \times I \to S^2$ durch $H(x,t) = (1-t)f(x)$.
Diese ist stetig, da $f$ stetig ist. Außerdem ist $H(x,0) = f(x)$ 
und $H(x,1) = 0$ für alle $x \in S^1$. Somit ist $f$ nullhomotop
und $S^2$ einfach-zusammenhängend.
-/

-- definiere ℝ×ℝ×ℝ als topologischen Raum
example : topological_space (ℝ×ℝ×ℝ) := by apply_instance 

-- definiere ℝ×ℝ×ℝ als metrischen Raum
instance : metric_space (ℝ×ℝ×ℝ) := by apply_instance

lemma north_pole_in_S2 : ((1,0,0):ℝ×ℝ×ℝ) ∈ S2 :=
begin
  -- zeige, dass ‖(1,0,0)‖ = 1 ist
  unfold S2,
  simp,
  unfold norm,
  simp,
end

-- Definiere einen Pfad vom 
noncomputable
def path_from_north_pole_to_point (y:ℝ×ℝ×ℝ) : ↥(I) → ℝ×ℝ×ℝ := λ t,
  if y = (-1,0,0) then
    (real.cos (coe t * real.pi), real.sin (coe t * real.pi), 0)
  else
    let v := (1 - (coe t : ℝ)) • (1,0,0) + (coe t : ℝ) • y in
    (1 / ‖v‖) • v

lemma north_pole_is_start_of_path_from_north_pole_to_point (y: ℝ×ℝ×ℝ) (hy: y ∈ S2): path_from_north_pole_to_point y (0 : unit_interval) = (1, 0, 0) :=
begin
  -- Hier möchten wir zeigen, dass (1,0,0) die Quelle von `path_from_north_pole_to_point` ist.
  unfold path_from_north_pole_to_point,
  simp,
  unfold norm,
  simp,
end

lemma end_of_path_from_north_pole_to_point_is_point (y: ℝ×ℝ×ℝ) (hy: y ∈ S2): path_from_north_pole_to_point y (1 : unit_interval) = y :=
begin
  unfold path_from_north_pole_to_point,
  -- Hier möchten wir zeigen, dass wir auf jeden Fall am Ende unseres Pfades bei y ankommen.
  -- Wir haben zwei fälle: y = (1,0,0) und y ≠ (1,0,0)
  -- Wir müssen einen extra Fall für y = (1,0,0) machen,
  -- unser Pfad in diesem fall besonders definiert werden muss,
  --  damit keine Singularität auftritt.
  cases eq_or_ne y (-1, 0, 0) with h h,
  {
    simp [h],
  },
  {
    -- wenn y ≠ (1,0,0)
    rw if_neg h,
    -- wir möchten hier zeigen, dass wenn wir y durch die Norm von y teilen,
    -- dass y wieder rauskommt, wenn y in S2 liegt
    simp [S2] at hy,
    simp [hy],
  },
end

lemma path_from_northpole_to_point_in_S2 (y: ℝ×ℝ×ℝ) (hy: y ∈ S2): ∀ t : ↥unit_interval, path_from_north_pole_to_point y t ∈ S2 :=
begin
  unfold path_from_north_pole_to_point,
  cases eq_or_ne y (-1, 0, 0) with h h,
  {
    -- wenn y = (-1,0,0)
    -- dann ist die Funktion einfach die konstante Funktion (1,0,0)
    -- und diese ist stetig
    simp [h],
    -- wir müssen zeigen, dass f in jeder der drei koodinaten stetig ist
    -- wir werden dabei zuerst auf die Zwei verschiedenen Fälle von f aufteilen
    -- 
    -- 1. y = (-1,0,0)
    -- 2. y ≠ (-1,0,0)

    -- wandle 
    -- ```
    -- ∀ (x : ℝ), 0 ≤ x →  ...
    -- ```
    -- in die assumption `hx : 0 ≤ x` um
    intros x hx₁ hx₂,


    -- zeige, dass
    -- ```
    -- (real.cos (x * real.pi), real.sin (x * real.pi), 0) ∈ S2
    -- ```

    unfold S2,
    simp,

    -- split,
    -- {
    --   -- wir müssen zeigen, dass die 1. koodinate stetig ist
    --   -- zeige, dass die cosinus funktion stetig ist
    --   by continuity,
    -- },
    -- {
    --   split,
    --   {
    --     -- wir müssen zeigen, dass die 2. koodinate stetig ist
    --     -- zeige, dass die sinus funktion stetig ist
    --     by continuity,
    --   },
    --   {
    --     -- wir müssen zeigen, dass die 3. koodinate stetig ist
    --     -- Zeige, dass die konstante 0 funktion stetig ist
    --     by continuity,
    --   }
    -- },
    sorry
  },
  {
  sorry,
  }
end

-- Zeige, dass das inverse der norm stetig ist, wenn der vektor in der norm nicht 0 wird
lemma norm_inv_continuous (x: ℝ×ℝ×ℝ) (hx: x ≠ (0,0,0)):  continuous (λ x : ℝ × ℝ × ℝ, ‖x‖⁻¹ : ℝ × ℝ × ℝ → ℝ) :=
begin
  sorry,
end

lemma path_from_north_pole_to_point_is_continuous (y: ℝ×ℝ×ℝ) (hy: y ∈ S2): continuous (path_from_north_pole_to_point y) :=
begin
  -- Wir möchten zeigen, dass die Funktion stetig ist.
  -- weil diese als if-then-else definiert ist, müssen wir zwei fälle betrachten:
  unfold path_from_north_pole_to_point,
  cases eq_or_ne y (-1, 0, 0) with h h,
  {
    -- wenn y = (-1,0,0)
    -- dann ist die Funktion einfach die konstante Funktion (1,0,0)
    -- und diese ist stetig
    simp [h],
    -- wir müssen zeigen, dass f in jeder der drei koodinaten stetig ist
    -- wir werden dabei zuerst auf die Zwei verschiedenen Fälle von f aufteilen
    -- 
    -- 1. y = (-1,0,0)
    -- 2. y ≠ (-1,0,0)
    split,
    {
      -- wir müssen zeigen, dass die 1. koodinate stetig ist
      -- zeige, dass die cosinus funktion stetig ist
      by continuity,
    },
    {
      split,
      {
        -- wir müssen zeigen, dass die 2. koodinate stetig ist
        -- zeige, dass die sinus funktion stetig ist
        by continuity,
      },
      {
        -- wir müssen zeigen, dass die 3. koodinate stetig ist
        -- Zeige, dass die konstante 0 funktion stetig ist
        by continuity,
      }
    },
  },
  {
  -- simp [h],
  -- apply continuous.add,
  -- simp [h],
  
  -- sorry,
    simp [h],
    -- wenn y ≠ (-1,0,0)
    -- dann ist die Funktion etwas komplizierter definiert:
    --
    -- ```
    -- continuous (λ (t : ↥unit_interval), (‖(1 - ↑t, 0, 0) + ↑t • y‖⁻¹ * (1 - ↑t), 0, 0) + ‖(1 - ↑t, 0, 0) + ↑t • y‖⁻¹ • ↑t • y)
    -- ```
    --
    -- wir müssen zeigen, dass sie stetig ist
    -- Wir verwenden `continuous.add`, um zu zeigen, dass die Funktion stetig ist.
    -- Der Trick ist hier, dass unsere Funktion :
    -- (λ (t : ↥unit_interval), (‖(1 - ↑t, 0, 0) + ↑t • y‖⁻¹ * (1 - ↑t), 0, 0) + ‖(1 - ↑t, 0, 0) + ↑t • y‖⁻¹ • ↑t • y)
    -- in die Summanden
    -- 1. (‖(1 - ↑t, 0, 0) + ↑t • y‖⁻¹ * (1 - ↑t), 0, 0)
    -- 2. ‖(1 - ↑t, 0, 0) + ↑t • y‖⁻¹ • ↑t • y)
    -- aufgeteilt werden kann.
    apply continuous.add,
    {
      -- # Fall 1
      -- 1. (‖(1 - ↑t, 0, 0) + ↑t • y‖⁻¹ * (1 - ↑t), 0, 0)
      --
      -- Schreiben wir dies wie einen normalen (Spalten-)Vektor 
      -- 
      -- / ‖(1 - ↑t, 0, 0) + ↑t • y‖⁻¹ * (1 - ↑t) \
      -- |                    0                   |
      -- \                    0                   /
      --
      -- wir möchten also die Stetigkeit in jeder der einzelnen
      -- Koordinaten zeigen
      simp [h], -- hiermit spalten wir die `continuous (x,y,z)` in eine `continuous x` und `continuous y` und `continuous z` auf
      split,
      {
        -- continuous (λ (x : ↥unit_interval), ‖(1 - ↑x, 0, 0) + ↑x • y‖⁻¹ * (1 - ↑x))
        --
        -- Teile auf in die Faktoren:
        -- 1. ‖(1 - ↑x, 0, 0) + ↑x • y‖⁻¹
        -- 2. (1 - ↑x)
        -- 🔥: hier zuest `continuous.` auf [https://leanprover-community.github.io/mathlib_docs/] suchen
        --     dann `continuous.mul` finden 
        --     dann danach auf github suchen [https://github.com/search?utf8=%E2%9C%93&q=continuous.mul&type=code]
        apply continuous.mul,
        {
          -- 1️⃣
          -- Wir möchten zeigen, dass
          --   ‖(1 - ↑x, 0, 0) + ↑x • y‖⁻¹
          -- die invertierte Norm stetig ist
          sorry,
        },
        {
          -- 2. (1 - ↑x)
          -- zeige, dass die Funktion stetig ist
          by continuity,
          -- FERTIG :)
        }
      },
      {
        -- Zeigen, dass die konstante Nullfunktion stetig ist
        by continuity,
      }
    },
    {
      -- 2️⃣
      -- Wir möchten nun zeigen, dass
      --    ‖(1 - ↑t, 0, 0) + ↑t • y‖⁻¹ • ↑t • y)
      -- stetig ist.
      apply continuous.smul,
      {
        sorry
      },
      {
        -- zeigen, dass skalarmultiplikation stetig ist
        by continuity,
      }
    }
  }
end

lemma S2_path_connected : is_path_connected S2 :=
begin
    unfold is_path_connected,
    use (1,0,0),
    split,
    exact north_pole_in_S2,
    {
      intro y,
      intro hy,
      -- decompose y into y1, y2, y3
      -- cases y with y1 y23,
      -- cases y23 with y2 y3,
      -- let y := (y1,y2,y3),
      unfold joined_in,
      -- Wir möchten nun den Pfad von (1,0,0) nach y konstruieren.
      let f : path (1,0,0) y := {
        -- betrachte die Definition von `path` mit <kbd>ctrl</kbd>+<kbd>click</kbd> auf `path`
        -- wir brauchen also auf jeden fall:
        source' := by exact north_pole_is_start_of_path_from_north_pole_to_point y hy,
        target' := by exact end_of_path_from_north_pole_to_point_is_point y hy,
        -- außerdem steht dort `extends C(I, X)`, also brauchen wir noch:
        -- hier soll eine funktion definiert werden, welche [0,1] nach ℝ×ℝ×ℝ geht
        -- sie soll für t = 0 den wert (1,0,0) haben und für t = 1 den wert y
        -- wir müssen auf jeden Fall für jeden wert t zwischen 0 und 1 einen wert p in ℝ×ℝ×ℝ haben, mit ‖p‖ = 1
        to_fun := path_from_north_pole_to_point y,
        continuous_to_fun := by exact path_from_north_pole_to_point_is_continuous y hy,
      },
      use f,
      intro y',
      simp,
      unfold S2,
      simp,
      -- wir müssen hier zeigen, dass f(t) immer in S2 liegt (also ‖f(t)‖ = 1
      -- sorry,
      -- unfold norm,
      -- simp,
      apply path_from_northpole_to_point_in_S2 y hy,
    }
end

lemma S2_loops_nullhomotopic : ∀ (γ : path ((1, 0, 0) : ℝ×ℝ×ℝ ) (1, 0, 0)), γ ∈ loops ((1, 0, 0) : ℝ×ℝ×ℝ) → is_homotopic_to γ (path.refl (1, 0, 0)) := 
begin
  intro γ,
  intro hγ,
  unfold is_homotopic_to,
  let trivialPath : path (1,0,0) (1,0,0) := {
    source' := by simp,
    target' := by simp,
    to_fun := λ t, (1,0,0),
    continuous_to_fun := by continuity,
  },
  let f := (λ γ': path (1,0,0) (1,0,0), trivialPath),
  let f' := (λ x, x),
  use f',
  split,
  {
    by continuity,
  },
  {
    unfold path.refl,
    sorry
  }
end

-- 🛑 Hier ist das HAUPTRESULTAT: S2 ist einfach-zusammenhängend
example : @ is_simply_connected _ _ (1,0,0) S2 _ :=
begin
  unfold is_simply_connected,
  -- Wir müssen per Definition von `is_simply_connected` zeigen, dass
  -- * `is_path_connected S2` gilt
  -- * `∀ (γ : path (1, 0, 0) (1, 0, 0)), γ ∈ loops (1, 0, 0) → is_homotopic_to γ (path.refl (1, 0, 0))`
  --   Also, jede Schleife von (1,0,0) homotop zu `path.refl (1,0,0)` (dem konstanten Pfad bei (1,0,0)) ist
  split,
  exact S2_path_connected, -- 1. Teil
  exact S2_loops_nullhomotopic, -- 2. Teil
  -- FERTIG :)
end