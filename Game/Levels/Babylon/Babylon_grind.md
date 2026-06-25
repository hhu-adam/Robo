1. (AllowFullGrind) Babylon/L04: use `grind` to solve `Icc 3 n \sub Icc 0 n` and discuss three cases `i = 0 \or i = 1 \or i = 2`.
2. Babylon/L05: `grind [Odd.neg_pow]` closes the goal
  `∀ x ∈ I, x ∉ {i ∈ I | Even i} → (-1) ^ x + 1 = 0`.
  `grind [Even.neg_pow]` closes the goal
  `∀ i ∈ {i ∈ I | Even i}, (-1) ^ i + 1 = 2`.
3. Babylon/L06: after `rw [← insert_Icc_right_eq_Icc_add_one]`
  `grind` close the goal. (Problem: using induction hypothesis implicitly; Solution: (ematch := 0)).
4. Babylon/L07: after `rw [← insert_Icc_left_eq_Icc_sub_one]`,
  same problem as above.
5. Babylon/L08: after `rw [← insert_Icc_right_eq_Icc_add_one]` same problem as above.
6. Babylon/L09: after `rw [← insert_Icc_right_eq_Icc_add_one]` then `grind [arithmetic_sum]`. Same problem as above.
