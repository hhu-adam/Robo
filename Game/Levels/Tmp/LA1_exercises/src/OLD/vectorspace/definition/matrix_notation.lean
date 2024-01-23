
-- -- Dadurch wird das Symbol für Matrixmultiplikation verfügbar.
-- open_locale matrix

-- /- ## Rechnen mit Vektoren und Matrizen

-- Reele Vektorräume definiert man in Lean am besten als Funktion von einem Indexset.

-- So ist `fin 2` eine Menge, die nur `0` und `1` enthält und `ℝ²` wird als `fin 2 → ℝ` definiert.

-- Das mag auf den ersten Blick etwas unintuitiv erscheinen, hat aber den Vorteil, dass man die ganze
-- Infrastruktur für Funktionen einfach direkt für Vektoren und Matrizen mitgebrauchen kann.
-- -/
-- notation `ℚ²` := fin 2 → ℚ -- euclidean_space ℝ (fin 2)
-- notation `ℚ³` := fin 3 → ℚ -- euclidean_space ℝ (fin 2)
-- notation `ℚ^(` n `)` := (fin n) → ℚ -- euclidean_space ℝ (fin 2)
-- notation `ℚ^(` j, i `)` := matrix (fin j) (fin i) ℚ -- euclidean_space ℝ (fin 2)

-- def A : ℚ^(3,2) := ![![ 2, 3],
--                      ![ 0, 1],
--                      ![-1, 0]]

-- def B : ℚ^(5,3) := !![ 2, 3.5, 1  ;
--                        0, 1  , 4  ;
--                       -1, 0.6, 8  ;
--                        3, 3  , 3.4;
--                        0, 9  , 1  ]

-- def C : ℚ^(3,3) := ![![ 2, 3, 4],
--                      ![ 0, 1, 3],
--                      ![-1, 0, 1]]

-- def x : ℚ² := ![4, 2]
-- def y : ℚ³ := ![4, 2, 0.1]

-- #eval (B ⬝ A)

-- -- Dot product
-- #eval A ⬝ᵥ A
-- #eval x ⬝ᵥ x

-- -- Cross Product
-- #eval y ×₃ y

-- -- Matrix-vector
-- #check matrix.mul_vec A x

-- -- Noch was anderes
-- #eval (matrix.col y) ⬝ (matrix.row y)
-- #eval y ⬝ᵥ y

-- -- Transposed matrix
-- #check Aᵀ

-- instance pointwise_mul: has_mul ℚ^(3,2) :=
-- ⟨λ A B j i, (A j i) * (B j i)⟩

-- example : has_add ℚ^(3,2) := infer_instance


-- instance pointwise_non_unital_ring : non_unital_ring ℚ^(3,2) :=
-- sorry