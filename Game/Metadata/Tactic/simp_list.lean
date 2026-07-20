import Game.Metadata.Tactic.Simp
import Game.Metadata.FromMathlib

-- Babylon, L01_Sum_Simp_Card:
attribute [game_simp] Finset.sum_const smul_eq_mul mul_one eq_self

-- Babylon, L02_Card2:
attribute [game_simp] Finset.sum_const smul_eq_mul

-- Babylon, L03_sum_congr:
attribute [game_simp] Finset.sum_const nsmul_eq_mul MulZeroClass.mul_zero eq_self

-- Babylon, L04_sum_subset:
attribute [game_simp] Finset.mem_Icc zero_le true_and not_and not_le

-- Babylon, L05_sum_subset2:
attribute [game_simp] Finset.filter_subset Finset.mem_filter not_and Nat.not_even_iff_odd Int.reduceNeg eq_self Finset.sum_const nsmul_eq_mul

-- Babylon, L06_Induction_sum_insert__arithmetic_sum:
attribute [game_simp] Finset.Icc_self Finset.sum_singleton CharP.cast_eq_zero one_div MulZeroClass.mul_zero zero_add mul_one eq_self Nat.cast_add Nat.cast_one Finset.mem_Icc zero_le add_le_iff_nonpos_right nonpos_iff_eq_zero one_ne_zero and_false not_false_eq_true

-- Babylon, L07_Induction2_sum_insert2:
attribute [game_simp] CharP.cast_eq_zero neg_zero Finset.Icc_self Finset.sum_singleton eq_self Nat.cast_add Nat.cast_one neg_add_rev Int.reduceNeg Finset.mem_Icc le_sub_self_iff Int.reduceLE tsub_le_iff_right false_and not_false_eq_true add_neg_le_iff_le_add add_le_iff_nonpos_right and_false

-- Babylon, L08_Induction3_sub_insert3:
attribute [game_simp] Finset.Icc_self Finset.sum_singleton MulZeroClass.mul_zero zero_add one_pow eq_self Finset.mem_Icc zero_le add_le_iff_nonpos_right nonpos_iff_eq_zero one_ne_zero and_false not_false_eq_true

-- Babylon, L09_Boss:
attribute [game_simp] Finset.Icc_self Finset.sum_singleton CharP.cast_eq_zero ne_eq OfNat.ofNat_ne_zero not_false_eq_true zero_pow eq_self Nat.cast_add Nat.cast_one Finset.mem_Icc zero_le add_le_iff_nonpos_right nonpos_iff_eq_zero one_ne_zero and_false Finset.sum_insert one_div

-- Cantor, L01_CantorPowerset:
attribute [game_simp] Set.mem_setOf_eq

-- Cantor, L02_CantorPowerset:
attribute [game_simp] Set.mem_setOf_eq

-- Cantor, L03_IsFixedPt_abs:
attribute [game_simp] abs_nonneg abs_eq_self

-- Cantor, L04_fixedPoints_neg:
attribute [game_simp] CharZero.neg_eq_self_iff Set.setOf_eq_eq_singleton eq_self

-- Cantor, L05_IsFixedPt_not:
attribute [game_simp] eq_iff_iff not_iff_self exists_const not_false_eq_true

-- Cantor, L06_IsFixedPt_odd:
attribute [game_simp] neg_inj

-- Cantor, L07_idempotent:
attribute [game_simp] Set.setOf_subset_setOf forall_exists_index forall_apply_eq_imp_iff Set.mem_setOf_eq Function.comp_apply

-- Cantor, L09_CantorDiag:
attribute [game_simp] Set.mem_setOf_eq

-- Cantor, L10_CantorPowerset:
attribute [game_simp] eq_iff_iff not_iff_self Set.setOf_false Set.mem_empty_iff_false

-- Cantor, L11_SequenceUncountable:
attribute [game_simp] Nat.succ_eq_add_one Nat.add_eq_left one_ne_zero Set.setOf_false Set.mem_empty_iff_false

-- Epo, L01_Surjective:
attribute [game_simp] sub_add_cancel eq_self

-- Epo, L02_CurrySurjective:
attribute [game_simp] Classical.not_forall not_exists ne_eq iff_self

-- Epo, L05_RightInverse:
attribute [game_simp] sub_add_sub_cancel

-- Euklid, L02_prod_insert:
attribute [game_simp] Finset.mem_erase ne_eq eq_self not_true_eq_false false_and not_false_eq_true

-- Euklid, L03_Finite_toFinset__prod_insert2:
attribute [game_simp] Set.Finite.mem_toFinset Set.mem_setOf_eq Finset.mem_erase ne_eq eq_self not_true_eq_false false_and not_false_eq_true

-- Euklid, L04_Boss_infinitely_many_primes:
attribute [game_simp] Set.Finite.mem_toFinset Set.mem_setOf_eq lt_add_iff_pos_left gt_iff_lt Finset.mem_erase ne_eq eq_self not_true_eq_false false_and not_false_eq_true

-- Iso, L01_Bijective:
attribute [game_simp] add_left_inj sub_add_cancel eq_self

-- Luna, L06_Icc__Icc_insert_succ_right:
attribute [game_simp] Finset.mem_insert Finset.mem_Icc

-- Luna, L08_Omega3:
attribute [game_simp] Finset.mem_sdiff Finset.mem_Icc zero_le true_and not_and not_le

-- Luna, L10_Icc_subset_Icc_iff:
attribute [game_simp] Finset.mem_Icc and_imp

-- Mono, L01_Injective:
attribute [game_simp] add_left_inj imp_self

-- Mono, L05_StrictMono:
attribute [game_simp] add_lt_add_iff_right imp_self

-- Mono, L07_SuccHasLeftInv:
attribute [game_simp] Nat.succ_eq_add_one add_tsub_cancel_right eq_self implies_true

-- Mono, L11_InjHasLeftInv:
attribute [game_simp] exists_apply_eq_apply reduceDIte

-- Piazza, L02_Simp:
attribute [game_simp] Set.mem_setOf_eq

-- Piazza, L03_Ext__Set__Union__Inter:
attribute [game_simp] Set.mem_inter_iff Set.mem_union

-- Piazza, L04_Generalize__univ__eq_univ_iff_forall:
attribute [game_simp] Set.mem_union Set.mem_setOf_eq

-- Piazza, L05_empty__eq_empty_iff_forall_notMem:
attribute [game_simp] Set.mem_inter_iff Set.mem_setOf_eq Set.mem_empty_iff_false iff_false not_and Nat.not_odd_iff_even imp_self implies_true

-- Piazza, L06_Ext2__univ2:
attribute [game_simp] Set.mem_diff Set.mem_univ Set.mem_inter_iff not_and true_and Set.mem_union

-- Piazza, L10:
attribute [game_simp] Set.mem_insert_iff Set.mem_singleton_iff Set.singleton_union Set.mem_setOf_eq

-- Piazza, L11_erase:
attribute [game_simp] Finset.mem_erase ne_eq Finset.mem_sdiff Finset.mem_singleton

-- Piazza, L12_insert:
attribute [game_simp] Finset.mem_insert Finset.union_singleton iff_self

-- Piazza, L13_insert_erase:
attribute [game_simp] Finset.mem_insert Finset.mem_erase ne_eq not_false_eq_true true_and false_or iff_self

-- Prado, L08_exists_prime_and_dvd:
attribute [game_simp] ne_eq OfNat.ofNat_ne_one not_false_eq_true

-- Prado, L10_EvenPrime:
attribute [game_simp] even_two and_true and_imp

-- Robotswana, L01_SMulEBasis:
attribute [game_simp] Matrix.smul_single smul_eq_mul mul_one eq_self

-- Robotswana, L02_EBasis:
attribute [game_simp] ne_eq not_false_eq_true Matrix.single_mul_single_of_ne eq_self

-- Robotswana, L03:
attribute [game_simp] Matrix.single_mul_single_same mul_one eq_self

-- Robotswana, L04_MatrixEqSum:
attribute [game_simp] Matrix.smul_single smul_eq_mul mul_one

-- Robotswana, L05_EBasisDiagSum:
attribute [game_simp] Finset.subset_univ Finset.sum_singleton Matrix.one_apply_eq Matrix.smul_apply smul_eq_mul one_mul eq_self Finset.mem_singleton ne_eq not_false_eq_true Matrix.one_apply_ne zero_smul

-- Robotswana, L06_EBasisEqOnDiag:
attribute [game_simp] Matrix.single_mul_single_same mul_one eq_self

-- Robotswana, L07_EBasisZeroOffDiag:
attribute [game_simp] Matrix.single_mul_single_same mul_one eq_self map_zero

-- Robotswana, L08_EvalOnEBasis:
attribute [game_simp] map_sum map_smul smul_eq_mul MulZeroClass.mul_zero eq_self Finset.sum_ite_eq Finset.mem_univ reduceIte

-- Robotswana, L09_EvalOnEBasis:
attribute [game_simp] Nat.cast_eq_zero Matrix.smul_single smul_eq_mul mul_one Finset.sum_const Finset.card_univ Fintype.card_fin nsmul_eq_mul eq_self Matrix.one_apply_eq one_mul

-- Robotswana, L10_Characterize:
attribute [game_simp] mul_one

-- Samarkand, L01_ImagePreimage:
attribute [game_simp] Set.mem_image Set.mem_preimage

-- Samarkand, L02_ImageMap:
attribute [game_simp] Function.comp_apply Set.mem_image exists_exists_and_eq_and iff_self

-- Samarkand, L04_SurjectiveImagePreimage:
attribute [game_simp] Set.mem_image Set.mem_preimage

-- Samarkand, L06_PreimageNonempty:
attribute [game_simp] Set.mem_preimage Set.mem_singleton_iff Classical.not_forall Classical.not_not iff_self

-- Samarkand, L08_Preimage_Injective:
attribute [game_simp] Set.mem_singleton_iff eq_self Set.mem_preimage Classical.not_forall Classical.not_not iff_self Set.preimage_empty ne_eq Set.singleton_ne_empty not_false_eq_true

-- Step, L02:
attribute [game_simp] Nat.succ_eq_add_one Nat.reduceAdd one_div Matrix.add_cons Matrix.head_cons Matrix.tail_cons Matrix.empty_add_empty Matrix.vecCons_inj eq_self and_true Fin.zero_eta Fin.isValue Pi.add_apply Matrix.cons_val_zero Fin.mk_one Matrix.cons_val_one Matrix.cons_val_fin_one

-- Step, L03_LinearCombination:
attribute [game_simp] Matrix.cons_val_zero Matrix.cons_val_one Finsupp.coe_equivFunOnFinite_symm zero_smul zero_mul

-- Step, L07:
attribute [game_simp] Pi.add_apply Pi.smul_apply smul_eq_mul

-- Step, L08:
attribute [game_simp] Pi.add_apply Pi.smul_apply zero_add smul_eq_mul zero_sub mul_neg Pi.zero_apply

-- Step, L09:
attribute [game_simp] neg_smul one_smul Pi.add_apply Pi.smul_apply smul_eq_mul Pi.neg_apply Pi.zero_apply

-- Step, L13:
attribute [game_simp] Finset.sum_empty eq_self Finset.notMem_empty IsEmpty.forall_iff implies_true imp_self lt_add_iff_pos_right zero_lt_one and_self

-- Vieta, L02_Function:
attribute [game_simp] Int.reducePow eq_self

-- Vieta, L03_Let:
attribute [game_simp] sub_lt_self_iff zero_lt_one

-- Vieta, L06_Piecewise:
attribute [game_simp] Function.comp_apply mul_ite MulZeroClass.mul_zero Nat.ofNat_pos mul_nonneg_iff_of_pos_left

-- Vieta, L07_Extend:
attribute [game_simp] Nat.cast_nonneg Int.toNat_natCast reduceIte eq_self

-- Vieta, L10_Surjective:
attribute [game_simp] Function.comp_apply Nat.succ_eq_add_one
