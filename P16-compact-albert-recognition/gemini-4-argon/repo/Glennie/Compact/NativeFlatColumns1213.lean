module

public import Glennie.Compact.FlatBase
public import Glennie.Compact.Rank20Reduction

@[expose] public section

namespace Glennie.Compact.NativeFlatColumns1213

open Glennie.Compact.NativeDictionary
open Glennie.Compact.FlatBase
open Glennie.Compact.FlowFamily
open Glennie.Compact.Rank20
open Glennie.Compact.Rank20Certificate

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

private theorem direction_twelve_flatFrameP (i : Fin 3) :
    direction 12 (flatFrameP i) =
      ![(⟨0, 0, 0, 0, (0, (⟨1 / 4, 0, 0, 0⟩ : Quaternion ℝ)), 0⟩ : Glennie.Albert),
        0,
        ⟨0, 0, 0, 0, (0, (⟨-1 / 4, 0, 0, 0⟩ : Quaternion ℝ)), 0⟩] i := by
  rw [direction, Glennie.Compact.innerDerLinear_apply, flatFrameP_literal i]
  fin_cases i <;> ext <;>
    norm_num [Glennie.Compact.innerDer, partnerBasis, diagonalAlbert, archivalHiddenBasis,
      hiddenAlbert, hiddenOct, jordan_d0, jordan_d1, jordan_d2,
      jordan_o01, jordan_o02, jordan_o12,
      octDot_coordinates, octNormSq, Quaternion.normSq_def', octMul, octConj, octScalar,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]

private theorem direction_thirteen_flatFrameP (i : Fin 3) :
    direction 13 (flatFrameP i) =
      ![(⟨0, 0, 0, 0, (0, (⟨0, 1 / 4, 0, 0⟩ : Quaternion ℝ)), 0⟩ : Glennie.Albert),
        0,
        ⟨0, 0, 0, 0, (0, (⟨0, -1 / 4, 0, 0⟩ : Quaternion ℝ)), 0⟩] i := by
  rw [direction, Glennie.Compact.innerDerLinear_apply, flatFrameP_literal i]
  fin_cases i <;> ext <;>
    norm_num [Glennie.Compact.innerDer, partnerBasis, diagonalAlbert, archivalHiddenBasis,
      hiddenAlbert, hiddenOct, jordan_d0, jordan_d1, jordan_d2,
      jordan_o01, jordan_o02, jordan_o12,
      octDot_coordinates, octNormSq, Quaternion.normSq_def', octMul, octConj, octScalar,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]

private theorem direction_fourteen_flatFrameP (i : Fin 3) :
    direction 14 (flatFrameP i) =
      ![(0 : Glennie.Albert),
        ⟨0, 0, 0, (0, (⟨-1 / 2, 0, 0, 0⟩ : Quaternion ℝ)), 0, 0⟩,
        ⟨0, 0, 0, (0, (⟨1 / 2, 0, 0, 0⟩ : Quaternion ℝ)), 0, 0⟩] i := by
  rw [direction, Glennie.Compact.innerDerLinear_apply, flatFrameP_literal i]
  fin_cases i <;> ext <;>
    norm_num [Glennie.Compact.innerDer, partnerBasis, diagonalAlbert, archivalHiddenBasis,
      hiddenAlbert, hiddenOct, jordan_d0, jordan_d1, jordan_d2,
      jordan_o01, jordan_o02, jordan_o12,
      octDot_coordinates, octNormSq, Quaternion.normSq_def', octMul, octConj, octScalar,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]

private theorem direction_fifteen_flatFrameP (i : Fin 3) :
    direction 15 (flatFrameP i) =
      ![(0 : Glennie.Albert),
        ⟨0, 0, 0, (0, (⟨0, -1 / 2, 0, 0⟩ : Quaternion ℝ)), 0, 0⟩,
        ⟨0, 0, 0, (0, (⟨0, 1 / 2, 0, 0⟩ : Quaternion ℝ)), 0, 0⟩] i := by
  rw [direction, Glennie.Compact.innerDerLinear_apply, flatFrameP_literal i]
  fin_cases i <;> ext <;>
    norm_num [Glennie.Compact.innerDer, partnerBasis, diagonalAlbert, archivalHiddenBasis,
      hiddenAlbert, hiddenOct, jordan_d0, jordan_d1, jordan_d2,
      jordan_o01, jordan_o02, jordan_o12,
      octDot_coordinates, octNormSq, Quaternion.normSq_def', octMul, octConj, octScalar,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]

private theorem flat_pair_o02_lower_re (j k : Fin 3) :
    (jordan (flatFrameQ j) (flatFrameR k)).o02.2.re =
      ![(flatScale / 6 : ℝ), 0, -flatScale / 6] k := by
  rw [flatFrameQ_literal j, flatFrameR_literal k]
  fin_cases j <;> fin_cases k <;>
    norm_num [jordan_o02, octMul,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;> ring

private theorem flat_pair_o02_lower_imI (j k : Fin 3) :
    (jordan (flatFrameQ j) (flatFrameR k)).o02.2.imI =
      ![(1 / 18 : ℝ), -1 / 9, 1 / 18] k := by
  rw [flatFrameQ_literal j, flatFrameR_literal k]
  fin_cases j <;> fin_cases k <;>
    norm_num [jordan_o02, octMul,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]

private theorem flat_pair_o01_lower_re (j k : Fin 3) :
    (jordan (flatFrameQ j) (flatFrameR k)).o01.2.re =
      ![![(-1 / 36 : ℝ), -1 / 36, 1 / 18],
        ![-1 / 36, 1 / 18, -1 / 36],
        ![1 / 18, -1 / 36, -1 / 36]] j k := by
  rw [flatFrameQ_literal j, flatFrameR_literal k]
  fin_cases j <;> fin_cases k <;>
    norm_num [jordan_o01, octMul, octConj,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;>
    ring_nf <;> norm_num [flatScale_sq]

private theorem flat_pair_o01_lower_imI (j k : Fin 3) :
    (jordan (flatFrameQ j) (flatFrameR k)).o01.2.imI =
      ![![(-flatScale / 12 : ℝ), flatScale / 12, 0],
        ![flatScale / 12, 0, -flatScale / 12],
        ![0, -flatScale / 12, flatScale / 12]] j k := by
  rw [flatFrameQ_literal j, flatFrameR_literal k]
  fin_cases j <;> fin_cases k <;>
    norm_num [jordan_o01, octMul, octConj,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;> ring

theorem jacobianEntry_flatBase_column_twelve (r : Fin 20) :
    jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r 12 = JQ r 12 := by
  rw [jacobianEntry_ctx0 _ r 12 (by rfl)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [direction_twelve_flatFrameP]
  fin_cases r <;>
    norm_num [rowIndex, inner_coordinates, octDot_coordinates,
      flat_pair_o02_lower_re, flatScale_eq_sqrt3_div_three, JQ, JZ] <;> ring

theorem jacobianEntry_flatBase_column_thirteen (r : Fin 20) :
    jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r 13 = JQ r 13 := by
  rw [jacobianEntry_ctx0 _ r 13 (by rfl)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [direction_thirteen_flatFrameP]
  fin_cases r <;>
    norm_num [rowIndex, inner_coordinates, octDot_coordinates, flat_pair_o02_lower_imI, JQ, JZ]

theorem jacobianEntry_flatBase_column_fourteen (r : Fin 20) :
    jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r 14 = JQ r 14 := by
  rw [jacobianEntry_ctx0 _ r 14 (by rfl)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [direction_fourteen_flatFrameP]
  fin_cases r <;>
    norm_num [rowIndex, inner_coordinates, octDot_coordinates, flat_pair_o01_lower_re, JQ, JZ]

theorem jacobianEntry_flatBase_column_fifteen (r : Fin 20) :
    jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r 15 = JQ r 15 := by
  rw [jacobianEntry_ctx0 _ r 15 (by rfl)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [direction_fifteen_flatFrameP]
  fin_cases r <;>
    norm_num [rowIndex, inner_coordinates, octDot_coordinates,
      flat_pair_o01_lower_imI, flatScale_eq_sqrt3_div_three, JQ, JZ] <;> ring

end
end Glennie.Compact.NativeFlatColumns1213
