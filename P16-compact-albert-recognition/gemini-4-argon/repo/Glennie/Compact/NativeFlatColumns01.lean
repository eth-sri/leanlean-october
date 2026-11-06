module

public import Glennie.Compact.FlatBase
public import Glennie.Compact.Rank20Reduction

@[expose] public section

namespace Glennie.Compact.NativeFlatColumns01

open Glennie.Compact.NativeDictionary
open Glennie.Compact.FlatBase
open Glennie.Compact.FlowFamily
open Glennie.Compact.Rank20
open Glennie.Compact.Rank20Certificate

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

private theorem direction_zero_flatFrameP (i : Fin 3) :
    direction 0 (flatFrameP i) =
      ![(0 : Albert),
        ⟨0, 0, 0, octScalar (1 / 2), 0, 0⟩,
        ⟨0, 0, 0, octScalar (-1 / 2), 0, 0⟩] i := by
  rw [direction, Glennie.Compact.innerDerLinear_apply, flatFrameP_literal i]
  fin_cases i <;> ext <;>
    norm_num [Glennie.Compact.innerDer, partnerBasis, diagonalAlbert, complexAlbert, complexOct,
      jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
      octDot_coordinates, octNormSq, Quaternion.normSq_def', octMul, octConj, octScalar,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;>
    simp only [← Quaternion.coe_inv, Quaternion.re_coe, Quaternion.imI_coe,
      Quaternion.imJ_coe, Quaternion.imK_coe] <;> norm_num

private theorem direction_one_flatFrameP (i : Fin 3) :
    direction 1 (flatFrameP i) =
      ![(0 : Albert),
        ⟨0, 0, 0, ((⟨0, 1 / 2, 0, 0⟩ : Quaternion ℝ), 0), 0, 0⟩,
        ⟨0, 0, 0, ((⟨0, -1 / 2, 0, 0⟩ : Quaternion ℝ), 0), 0, 0⟩] i := by
  rw [direction, Glennie.Compact.innerDerLinear_apply, flatFrameP_literal i]
  fin_cases i <;> ext <;>
    norm_num [Glennie.Compact.innerDer, partnerBasis, diagonalAlbert, complexAlbert, complexOct,
      jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
      octDot_coordinates, octNormSq, Quaternion.normSq_def', octMul, octConj, octScalar,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]

private theorem direction_two_flatFrameP (i : Fin 3) :
    direction 2 (flatFrameP i) =
      ![(⟨0, 0, 0, 0, octScalar (1 / 4), 0⟩ : Albert),
        0, ⟨0, 0, 0, 0, octScalar (-1 / 4), 0⟩] i := by
  rw [direction, Glennie.Compact.innerDerLinear_apply, flatFrameP_literal i]
  fin_cases i <;> ext <;>
    norm_num [Glennie.Compact.innerDer, partnerBasis, diagonalAlbert, complexAlbert, complexOct,
      jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
      octDot_coordinates, octNormSq, Quaternion.normSq_def', octMul, octConj, octScalar,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;>
    simp only [← Quaternion.coe_inv, Quaternion.re_coe, Quaternion.imI_coe,
      Quaternion.imJ_coe, Quaternion.imK_coe] <;> norm_num

private theorem direction_three_flatFrameP (i : Fin 3) :
    direction 3 (flatFrameP i) =
      ![(⟨0, 0, 0, 0, ((⟨0, 1 / 4, 0, 0⟩ : Quaternion ℝ), 0), 0⟩ : Albert),
        0, ⟨0, 0, 0, 0, ((⟨0, -1 / 4, 0, 0⟩ : Quaternion ℝ), 0), 0⟩] i := by
  rw [direction, Glennie.Compact.innerDerLinear_apply, flatFrameP_literal i]
  fin_cases i <;> ext <;>
    norm_num [Glennie.Compact.innerDer, partnerBasis, diagonalAlbert, complexAlbert, complexOct,
      jordan_d0, jordan_d1, jordan_d2, jordan_o01, jordan_o02, jordan_o12,
      octDot_coordinates, octNormSq, Quaternion.normSq_def', octMul, octConj, octScalar,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]

private theorem flat_pair_o01_re (j k : Fin 3) :
    (jordan (flatFrameQ j) (flatFrameR k)).o01.1.re =
      ![-flatScale / 6, 0, flatScale / 6] j := by
  rw [flatFrameQ_literal j, flatFrameR_literal k]
  fin_cases j <;> fin_cases k <;>
    norm_num [jordan_o01, octMul, octConj,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;> ring

private theorem flat_pair_o01_imI (j k : Fin 3) :
    (jordan (flatFrameQ j) (flatFrameR k)).o01.1.imI =
      ![(-1 / 18 : ℝ), 1 / 9, -1 / 18] j := by
  rw [flatFrameQ_literal j, flatFrameR_literal k]
  fin_cases j <;> fin_cases k <;>
    norm_num [jordan_o01, octMul, octConj,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]

private theorem flat_pair_o02_re (j k : Fin 3) :
    (jordan (flatFrameQ j) (flatFrameR k)).o02.1.re =
      ![(1 / 18 : ℝ), -1 / 9, 1 / 18] j := by
  rw [flatFrameQ_literal j, flatFrameR_literal k]
  fin_cases j <;> fin_cases k <;>
    norm_num [jordan_o02, octMul,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]

private theorem flat_pair_o02_imI (j k : Fin 3) :
    (jordan (flatFrameQ j) (flatFrameR k)).o02.1.imI =
      ![flatScale / 6, 0, -flatScale / 6] j := by
  rw [flatFrameQ_literal j, flatFrameR_literal k]
  fin_cases j <;> fin_cases k <;>
    norm_num [jordan_o02, octMul,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;> ring

theorem jacobianEntry_flatBase_column_zero (r : Fin 20) :
    jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r 0 = JQ r 0 := by
  rw [jacobianEntry_ctx0 _ r 0 (by rfl)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [direction_zero_flatFrameP]
  fin_cases r <;>
    norm_num [rowIndex, inner_coordinates, octDot_coordinates, octScalar,
      flat_pair_o01_re, flatScale_eq_sqrt3_div_three, JQ, JZ] <;>
    simp only [← Quaternion.coe_inv, Quaternion.re_coe, Quaternion.imI_coe,
      Quaternion.imJ_coe, Quaternion.imK_coe] <;> norm_num <;> ring

theorem jacobianEntry_flatBase_column_one (r : Fin 20) :
    jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r 1 = JQ r 1 := by
  rw [jacobianEntry_ctx0 _ r 1 (by rfl)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [direction_one_flatFrameP]
  fin_cases r <;>
    norm_num [rowIndex, inner_coordinates, octDot_coordinates, flat_pair_o01_imI, JQ, JZ]

theorem jacobianEntry_flatBase_column_two (r : Fin 20) :
    jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r 2 = JQ r 2 := by
  rw [jacobianEntry_ctx0 _ r 2 (by rfl)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [direction_two_flatFrameP]
  fin_cases r <;>
    norm_num [rowIndex, inner_coordinates, octDot_coordinates, octScalar,
      flat_pair_o02_re, JQ, JZ] <;>
    simp only [← Quaternion.coe_inv, Quaternion.re_coe, Quaternion.imI_coe,
      Quaternion.imJ_coe, Quaternion.imK_coe] <;> norm_num

theorem jacobianEntry_flatBase_column_three (r : Fin 20) :
    jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r 3 = JQ r 3 := by
  rw [jacobianEntry_ctx0 _ r 3 (by rfl)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [direction_three_flatFrameP]
  fin_cases r <;>
    norm_num [rowIndex, inner_coordinates, octDot_coordinates,
      flat_pair_o02_imI, flatScale_eq_sqrt3_div_three, JQ, JZ] <;> ring

end
end Glennie.Compact.NativeFlatColumns01
