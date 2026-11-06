module

public import Glennie.Compact.FlatBase
public import Glennie.Compact.Rank20Reduction

@[expose] public section

namespace Glennie.Compact.NativeFlatColumns89

open Glennie.Compact.NativeDictionary
open Glennie.Compact.FlatBase
open Glennie.Compact.FlowFamily
open Glennie.Compact.Rank20
open Glennie.Compact.Rank20Certificate

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

private theorem direction_eight_flatFrameP (i : Fin 3) :
    direction 8 (flatFrameP i) =
      ![(0 : Glennie.Albert),
        ⟨0, 0, 0, ((⟨0, 0, -1 / 2, 0⟩ : Quaternion ℝ), 0), 0, 0⟩,
        ⟨0, 0, 0, ((⟨0, 0, 1 / 2, 0⟩ : Quaternion ℝ), 0), 0, 0⟩] i := by
  rw [direction, Glennie.Compact.innerDerLinear_apply, flatFrameP_literal i]
  fin_cases i <;> ext <;>
    norm_num [Glennie.Compact.innerDer, partnerBasis, diagonalAlbert, archivalHiddenBasis,
      hiddenAlbert, hiddenOct, jordan_d0, jordan_d1, jordan_d2,
      jordan_o01, jordan_o02, jordan_o12,
      octDot_coordinates, octNormSq, Quaternion.normSq_def', octMul, octConj, octScalar,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]

private theorem direction_nine_flatFrameP (i : Fin 3) :
    direction 9 (flatFrameP i) =
      ![(0 : Glennie.Albert),
        ⟨0, 0, 0, ((⟨0, 0, 0, -1 / 2⟩ : Quaternion ℝ), 0), 0, 0⟩,
        ⟨0, 0, 0, ((⟨0, 0, 0, 1 / 2⟩ : Quaternion ℝ), 0), 0, 0⟩] i := by
  rw [direction, Glennie.Compact.innerDerLinear_apply, flatFrameP_literal i]
  fin_cases i <;> ext <;>
    norm_num [Glennie.Compact.innerDer, partnerBasis, diagonalAlbert, archivalHiddenBasis,
      hiddenAlbert, hiddenOct, jordan_d0, jordan_d1, jordan_d2,
      jordan_o01, jordan_o02, jordan_o12,
      octDot_coordinates, octNormSq, Quaternion.normSq_def', octMul, octConj, octScalar,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]

private theorem direction_ten_flatFrameP (i : Fin 3) :
    direction 10 (flatFrameP i) =
      ![(⟨0, 0, 0, 0, 0, (0, (⟨1 / 4, 0, 0, 0⟩ : Quaternion ℝ))⟩ : Glennie.Albert),
        ⟨0, 0, 0, 0, 0, (0, (⟨-1 / 4, 0, 0, 0⟩ : Quaternion ℝ))⟩,
        0] i := by
  rw [direction, Glennie.Compact.innerDerLinear_apply, flatFrameP_literal i]
  fin_cases i <;> ext <;>
    norm_num [Glennie.Compact.innerDer, partnerBasis, diagonalAlbert, archivalHiddenBasis,
      hiddenAlbert, hiddenOct, jordan_d0, jordan_d1, jordan_d2,
      jordan_o01, jordan_o02, jordan_o12,
      octDot_coordinates, octNormSq, Quaternion.normSq_def', octMul, octConj, octScalar,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]

private theorem direction_eleven_flatFrameP (i : Fin 3) :
    direction 11 (flatFrameP i) =
      ![(⟨0, 0, 0, 0, 0, (0, (⟨0, 1 / 4, 0, 0⟩ : Quaternion ℝ))⟩ : Glennie.Albert),
        ⟨0, 0, 0, 0, 0, (0, (⟨0, -1 / 4, 0, 0⟩ : Quaternion ℝ))⟩,
        0] i := by
  rw [direction, Glennie.Compact.innerDerLinear_apply, flatFrameP_literal i]
  fin_cases i <;> ext <;>
    norm_num [Glennie.Compact.innerDer, partnerBasis, diagonalAlbert, archivalHiddenBasis,
      hiddenAlbert, hiddenOct, jordan_d0, jordan_d1, jordan_d2,
      jordan_o01, jordan_o02, jordan_o12,
      octDot_coordinates, octNormSq, Quaternion.normSq_def', octMul, octConj, octScalar,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]

private theorem flat_pair_o01_imJ (j k : Fin 3) :
    (jordan (flatFrameQ j) (flatFrameR k)).o01.1.imJ =
      ![![(1 / 18 : ℝ), -1 / 36, -1 / 36],
        ![-1 / 36, 1 / 18, -1 / 36],
        ![-1 / 36, -1 / 36, 1 / 18]] j k := by
  rw [flatFrameQ_literal j, flatFrameR_literal k]
  fin_cases j <;> fin_cases k <;>
    norm_num [jordan_o01, octMul, octConj,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;>
    ring_nf <;> norm_num [flatScale_sq]

private theorem flat_pair_o01_imK (j k : Fin 3) :
    (jordan (flatFrameQ j) (flatFrameR k)).o01.1.imK =
      ![![(0 : ℝ), -flatScale / 12, flatScale / 12],
        ![flatScale / 12, 0, -flatScale / 12],
        ![-flatScale / 12, flatScale / 12, 0]] j k := by
  rw [flatFrameQ_literal j, flatFrameR_literal k]
  fin_cases j <;> fin_cases k <;>
    norm_num [jordan_o01, octMul, octConj,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;> ring

private theorem flat_pair_o12_lower_re (j k : Fin 3) :
    (jordan (flatFrameQ j) (flatFrameR k)).o12.2.re =
      ![![(-1 / 18 : ℝ), 1 / 36, 1 / 36],
        ![1 / 36, -1 / 18, 1 / 36],
        ![1 / 36, 1 / 36, -1 / 18]] j k := by
  rw [flatFrameQ_literal j, flatFrameR_literal k]
  fin_cases j <;> fin_cases k <;>
    norm_num [jordan_o12, octMul, octConj,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;>
    ring_nf <;> norm_num [flatScale_sq]

private theorem flat_pair_o12_lower_imI (j k : Fin 3) :
    (jordan (flatFrameQ j) (flatFrameR k)).o12.2.imI =
      ![![(0 : ℝ), flatScale / 12, -flatScale / 12],
        ![-flatScale / 12, 0, flatScale / 12],
        ![flatScale / 12, -flatScale / 12, 0]] j k := by
  rw [flatFrameQ_literal j, flatFrameR_literal k]
  fin_cases j <;> fin_cases k <;>
    norm_num [jordan_o12, octMul, octConj,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;> ring

theorem jacobianEntry_flatBase_column_eight (r : Fin 20) :
    jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r 8 = JQ r 8 := by
  rw [jacobianEntry_ctx0 _ r 8 (by rfl)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [direction_eight_flatFrameP]
  fin_cases r <;>
    norm_num [rowIndex, inner_coordinates, octDot_coordinates, flat_pair_o01_imJ, JQ, JZ]

theorem jacobianEntry_flatBase_column_nine (r : Fin 20) :
    jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r 9 = JQ r 9 := by
  rw [jacobianEntry_ctx0 _ r 9 (by rfl)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [direction_nine_flatFrameP]
  fin_cases r <;>
    norm_num [rowIndex, inner_coordinates, octDot_coordinates,
      flat_pair_o01_imK, flatScale_eq_sqrt3_div_three, JQ, JZ] <;> ring

theorem jacobianEntry_flatBase_column_ten (r : Fin 20) :
    jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r 10 = JQ r 10 := by
  rw [jacobianEntry_ctx0 _ r 10 (by rfl)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [direction_ten_flatFrameP]
  fin_cases r <;>
    norm_num [rowIndex, inner_coordinates, octDot_coordinates, flat_pair_o12_lower_re, JQ, JZ]

theorem jacobianEntry_flatBase_column_eleven (r : Fin 20) :
    jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r 11 = JQ r 11 := by
  rw [jacobianEntry_ctx0 _ r 11 (by rfl)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [direction_eleven_flatFrameP]
  fin_cases r <;>
    norm_num [rowIndex, inner_coordinates, octDot_coordinates,
      flat_pair_o12_lower_imI, flatScale_eq_sqrt3_div_three, JQ, JZ] <;> ring

end
end Glennie.Compact.NativeFlatColumns89
