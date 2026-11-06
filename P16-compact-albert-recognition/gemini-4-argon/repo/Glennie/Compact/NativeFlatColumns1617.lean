module

public import Glennie.Compact.FlatBase
public import Glennie.Compact.Rank20Reduction

@[expose] public section

namespace Glennie.Compact.NativeFlatColumns1617

open Glennie.Compact.NativeDictionary
open Glennie.Compact.FlatBase
open Glennie.Compact.FlowFamily
open Glennie.Compact.Rank20
open Glennie.Compact.Rank20Certificate

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

private theorem direction_sixteen_flatFrameQ (j : Fin 3) :
    direction 16 (flatFrameQ j) =
      ![(⟨0, 0, 0,
          ((⟨0, 0, -flatScale / 8, -1 / 24⟩ : Quaternion ℝ), 0), 0,
          ((⟨0, 0, flatScale / 8, -1 / 24⟩ : Quaternion ℝ), 0)⟩ : Glennie.Albert),
        ⟨0, 0, 0,
          ((⟨0, 0, 0, 1 / 12⟩ : Quaternion ℝ), 0), 0,
          ((⟨0, 0, 0, 1 / 12⟩ : Quaternion ℝ), 0)⟩,
        ⟨0, 0, 0,
          ((⟨0, 0, flatScale / 8, -1 / 24⟩ : Quaternion ℝ), 0), 0,
          ((⟨0, 0, -flatScale / 8, -1 / 24⟩ : Quaternion ℝ), 0)⟩] j := by
  rw [direction, Glennie.Compact.innerDerLinear_apply, flatFrameQ_literal j]
  fin_cases j <;> ext <;>
    norm_num [Glennie.Compact.innerDer, partnerBasis, diagonalAlbert, archivalHiddenBasis,
      hiddenAlbert, hiddenOct, jordan_d0, jordan_d1, jordan_d2,
      jordan_o01, jordan_o02, jordan_o12,
      octDot_coordinates, octNormSq, Quaternion.normSq_def', octMul, octConj, octScalar,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;> ring

private theorem direction_seventeen_flatFrameQ (j : Fin 3) :
    direction 17 (flatFrameQ j) =
      ![(⟨0, 0, 0,
          ((⟨0, 0, 1 / 24, -flatScale / 8⟩ : Quaternion ℝ), 0), 0,
          ((⟨0, 0, 1 / 24, flatScale / 8⟩ : Quaternion ℝ), 0)⟩ : Glennie.Albert),
        ⟨0, 0, 0,
          ((⟨0, 0, -1 / 12, 0⟩ : Quaternion ℝ), 0), 0,
          ((⟨0, 0, -1 / 12, 0⟩ : Quaternion ℝ), 0)⟩,
        ⟨0, 0, 0,
          ((⟨0, 0, 1 / 24, flatScale / 8⟩ : Quaternion ℝ), 0), 0,
          ((⟨0, 0, 1 / 24, -flatScale / 8⟩ : Quaternion ℝ), 0)⟩] j := by
  rw [direction, Glennie.Compact.innerDerLinear_apply, flatFrameQ_literal j]
  fin_cases j <;> ext <;>
    norm_num [Glennie.Compact.innerDer, partnerBasis, diagonalAlbert, archivalHiddenBasis,
      hiddenAlbert, hiddenOct, jordan_d0, jordan_d1, jordan_d2,
      jordan_o01, jordan_o02, jordan_o12,
      octDot_coordinates, octNormSq, Quaternion.normSq_def', octMul, octConj, octScalar,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;> ring

private theorem direction_eighteen_flatFrameQ (j : Fin 3) :
    direction 18 (flatFrameQ j) =
      ![(⟨0, 0, 0, 0,
          ((⟨0, 0, flatScale / 4, -1 / 12⟩ : Quaternion ℝ), 0),
          ((⟨0, 0, -1 / 12, flatScale / 4⟩ : Quaternion ℝ), 0)⟩ : Glennie.Albert),
        ⟨0, 0, 0, 0,
          ((⟨0, 0, 0, 1 / 6⟩ : Quaternion ℝ), 0),
          ((⟨0, 0, 1 / 6, 0⟩ : Quaternion ℝ), 0)⟩,
        ⟨0, 0, 0, 0,
          ((⟨0, 0, -flatScale / 4, -1 / 12⟩ : Quaternion ℝ), 0),
          ((⟨0, 0, -1 / 12, -flatScale / 4⟩ : Quaternion ℝ), 0)⟩] j := by
  rw [direction, Glennie.Compact.innerDerLinear_apply, flatFrameQ_literal j]
  fin_cases j <;> ext <;>
    norm_num [Glennie.Compact.innerDer, partnerBasis, diagonalAlbert, archivalHiddenBasis,
      hiddenAlbert, hiddenOct, jordan_d0, jordan_d1, jordan_d2,
      jordan_o01, jordan_o02, jordan_o12,
      octDot_coordinates, octNormSq, Quaternion.normSq_def', octMul, octConj, octScalar,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;> ring

private theorem direction_nineteen_flatFrameQ (j : Fin 3) :
    direction 19 (flatFrameQ j) =
      ![(⟨0, 0, 0, 0,
          ((⟨0, 0, 1 / 12, flatScale / 4⟩ : Quaternion ℝ), 0),
          ((⟨0, 0, -flatScale / 4, -1 / 12⟩ : Quaternion ℝ), 0)⟩ : Glennie.Albert),
        ⟨0, 0, 0, 0,
          ((⟨0, 0, -1 / 6, 0⟩ : Quaternion ℝ), 0),
          ((⟨0, 0, 0, 1 / 6⟩ : Quaternion ℝ), 0)⟩,
        ⟨0, 0, 0, 0,
          ((⟨0, 0, 1 / 12, -flatScale / 4⟩ : Quaternion ℝ), 0),
          ((⟨0, 0, flatScale / 4, -1 / 12⟩ : Quaternion ℝ), 0)⟩] j := by
  rw [direction, Glennie.Compact.innerDerLinear_apply, flatFrameQ_literal j]
  fin_cases j <;> ext <;>
    norm_num [Glennie.Compact.innerDer, partnerBasis, diagonalAlbert, archivalHiddenBasis,
      hiddenAlbert, hiddenOct, jordan_d0, jordan_d1, jordan_d2,
      jordan_o01, jordan_o02, jordan_o12,
      octDot_coordinates, octNormSq, Quaternion.normSq_def', octMul, octConj, octScalar,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;> ring

private theorem flat_pair_o01_upper_zero (i k : Fin 3) :
    (jordan (flatFrameP i) (flatFrameR k)).o01.1 = 0 := by
  rw [flatFrameP_literal i, flatFrameR_literal k]
  fin_cases i <;> fin_cases k <;> ext <;>
    norm_num [diagonalAlbert, jordan_o01, octMul, octConj,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]

private theorem flat_pair_o02_upper_zero (i k : Fin 3) :
    (jordan (flatFrameP i) (flatFrameR k)).o02.1 = 0 := by
  rw [flatFrameP_literal i, flatFrameR_literal k]
  fin_cases i <;> fin_cases k <;> ext <;>
    norm_num [diagonalAlbert, jordan_o02, octMul,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]

theorem flat_pair_o12_upper_JK (i k : Fin 3) :
    (jordan (flatFrameP i) (flatFrameR k)).o12.1 =
      ![![(⟨0, 0, -1 / 12, flatScale / 4⟩ : Quaternion ℝ),
          ⟨0, 0, 1 / 6, 0⟩, ⟨0, 0, -1 / 12, -flatScale / 4⟩],
        ![⟨0, 0, -1 / 12, flatScale / 4⟩,
          ⟨0, 0, 1 / 6, 0⟩, ⟨0, 0, -1 / 12, -flatScale / 4⟩],
        ![0, 0, 0]] i k := by
  rw [flatFrameP_literal i, flatFrameR_literal k]
  fin_cases i <;> fin_cases k <;> ext <;>
    norm_num [diagonalAlbert, jordan_o12, octMul, octConj,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] <;> ring

theorem jacobianEntry_flatBase_column_sixteen (r : Fin 20) :
    jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r 16 = JQ r 16 := by
  rw [jacobianEntry_ctx1 _ r 16 (by rfl)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [direction_sixteen_flatFrameQ]
  fin_cases r <;>
    norm_num [rowIndex, inner_coordinates, octDot_coordinates,
      flat_pair_o01_upper_zero, flat_pair_o12_upper_JK,
      flatScale_eq_sqrt3_div_three, JQ, JZ] <;> ring

theorem jacobianEntry_flatBase_column_seventeen (r : Fin 20) :
    jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r 17 = JQ r 17 := by
  rw [jacobianEntry_ctx1 _ r 17 (by rfl)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [direction_seventeen_flatFrameQ]
  fin_cases r <;>
    norm_num [rowIndex, inner_coordinates, octDot_coordinates,
      flat_pair_o01_upper_zero, flat_pair_o12_upper_JK, JQ, JZ] <;>
    ring_nf <;> norm_num [flatScale_sq]

theorem jacobianEntry_flatBase_column_eighteen (r : Fin 20) :
    jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r 18 = JQ r 18 := by
  rw [jacobianEntry_ctx1 _ r 18 (by rfl)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [direction_eighteen_flatFrameQ]
  fin_cases r <;>
    norm_num [rowIndex, inner_coordinates, octDot_coordinates,
      flat_pair_o02_upper_zero, flat_pair_o12_upper_JK, JQ, JZ] <;>
    ring_nf <;> norm_num [flatScale_sq]

theorem jacobianEntry_flatBase_column_nineteen (r : Fin 20) :
    jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r 19 = JQ r 19 := by
  rw [jacobianEntry_ctx1 _ r 19 (by rfl)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [direction_nineteen_flatFrameQ]
  fin_cases r <;>
    norm_num [rowIndex, inner_coordinates, octDot_coordinates,
      flat_pair_o02_upper_zero, flat_pair_o12_upper_JK,
      flatScale_eq_sqrt3_div_three, JQ, JZ] <;> ring

end
end Glennie.Compact.NativeFlatColumns1617
