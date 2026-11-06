/- Exactly original FlatBase columns8 and9, every Fin20 raw row including zeros.
   Original full-basis13/14 are NEGATIVE upper J/K in slot01. Actual ordered
   HALF commutators give (0,-1/2,+1/2), and BOTH conjugated slot01 mixed words
   precede JQ comparison. No desired Jacobian/derivative/trace/rank premise. -/
module

public import Glennie.Compact.FlatBase
public import Glennie.Compact.Rank20Reduction
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.Calculus.FDeriv.Linear

public import Glennie.Compact.NativeFlatCommon

@[expose] public section

namespace Glennie.Compact.NativeFlatColumns89

open Glennie.Compact.NativeFlatCommon
open Glennie.Compact.NativeDictionary
open Glennie.Compact.FlatBase
open Glennie.Compact.FlowFamily
open Glennie.Compact.Rank20
open Glennie.Compact.Rank20Certificate

noncomputable section

set_option maxHeartbeats 1000000 in
private theorem direction_eight_flatFrameP (i : Fin 3) :
    direction 8 (flatFrameP i) =
      ![(0 : Glennie.Albert),
        ⟨0, 0, 0,
          ((⟨0, 0, -1 / 2, 0⟩ : Quaternion ℝ), 0), 0, 0⟩,
        ⟨0, 0, 0,
          ((⟨0, 0, 1 / 2, 0⟩ : Quaternion ℝ), 0), 0, 0⟩] i := by
  have hp : partnerIndex (8 : Fin 20) = 13 := rfl
  rw [direction, hp, extDecode_extUnit_1, extDecode_extUnit_13,
    Glennie.Compact.innerDerLinear_apply, flatFrameP_literal i]
  fin_cases i <;> ext <;>
    norm_num [Glennie.Compact.innerDer, diagonalAlbert, archivalHiddenBasis,
      hiddenAlbert, hiddenOct, jordan_d0, jordan_d1, jordan_d2,
      jordan_o01, jordan_o02, jordan_o12,
      octDot_coordinates, octNormSq, Quaternion.normSq_def', octMul, octConj, octScalar,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul] <;>
    simp -failIfUnchanged only [← Quaternion.coe_inv, Quaternion.re_coe, Quaternion.imI_coe,
      Quaternion.imJ_coe, Quaternion.imK_coe] <;> norm_num

set_option maxHeartbeats 1000000 in
private theorem direction_nine_flatFrameP (i : Fin 3) :
    direction 9 (flatFrameP i) =
      ![(0 : Glennie.Albert),
        ⟨0, 0, 0,
          ((⟨0, 0, 0, -1 / 2⟩ : Quaternion ℝ), 0), 0, 0⟩,
        ⟨0, 0, 0,
          ((⟨0, 0, 0, 1 / 2⟩ : Quaternion ℝ), 0), 0, 0⟩] i := by
  have hp : partnerIndex (9 : Fin 20) = 14 := rfl
  rw [direction, hp, extDecode_extUnit_1, extDecode_extUnit_14,
    Glennie.Compact.innerDerLinear_apply, flatFrameP_literal i]
  fin_cases i <;> ext <;>
    norm_num [Glennie.Compact.innerDer, diagonalAlbert, archivalHiddenBasis,
      hiddenAlbert, hiddenOct, jordan_d0, jordan_d1, jordan_d2,
      jordan_o01, jordan_o02, jordan_o12,
      octDot_coordinates, octNormSq, Quaternion.normSq_def', octMul, octConj, octScalar,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul] <;>
    simp -failIfUnchanged only [← Quaternion.coe_inv, Quaternion.re_coe, Quaternion.imI_coe,
      Quaternion.imJ_coe, Quaternion.imK_coe] <;> norm_num

/- Whole actual Q/R literals are rederived from their projector definitions.
   No earlier private helper or assumed coordinate/value table is imported. -/
private theorem flat_pair_o01_imJ (j k : Fin 3) :
    (jordan (flatFrameQ j) (flatFrameR k)).o01.1.imJ =
      ![![(1 / 18 : ℝ), -1 / 36, -1 / 36],
        ![-1 / 36, 1 / 18, -1 / 36],
        ![-1 / 36, -1 / 36, 1 / 18]] j k := by
  rw [flatFrameQ_literal j, flatFrameR_literal k]
  fin_cases j <;> fin_cases k <;>
    norm_num [jordan_o01, octMul, octConj,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul] <;>
    ring_nf <;> norm_num [flatScale_sq]

private theorem flat_pair_o01_imK (j k : Fin 3) :
    (jordan (flatFrameQ j) (flatFrameR k)).o01.1.imK =
      ![![(0 : ℝ), -flatScale / 12, flatScale / 12],
        ![flatScale / 12, 0, -flatScale / 12],
        ![-flatScale / 12, flatScale / 12, 0]] j k := by
  rw [flatFrameQ_literal j, flatFrameR_literal k]
  fin_cases j <;> fin_cases k <;>
    norm_num [jordan_o01, octMul, octConj,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul] <;> ring

theorem jacobianEntry_flatBase_column_eight (r : Fin 20) :
    jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r 8 = JQ r 8 := by
  rw [jacobianEntry_ctx0 _ r 8 (by rfl)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [direction_eight_flatFrameP]
  fin_cases r <;>
    norm_num [rowIndex, inner_coordinates, octDot_coordinates,
      flat_pair_o01_imJ, JQ, JZ] <;>
    simp -failIfUnchanged only [← Quaternion.coe_inv, Quaternion.re_coe, Quaternion.imI_coe,
      Quaternion.imJ_coe, Quaternion.imK_coe] <;> norm_num <;> ring

set_option maxHeartbeats 1000000 in
/-- All20 original raw rows of column9, including its twelve zeros. -/
theorem jacobianEntry_flatBase_column_nine (r : Fin 20) :
    jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r 9 = JQ r 9 := by
  rw [jacobianEntry_ctx0 _ r 9 (by rfl)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [direction_nine_flatFrameP]
  fin_cases r <;>
    norm_num [rowIndex, inner_coordinates, octDot_coordinates,
      flat_pair_o01_imK, flatScale_eq_sqrt3_div_three, JQ, JZ] <;>
    simp -failIfUnchanged only [← Quaternion.coe_inv, Quaternion.re_coe, Quaternion.imI_coe,
      Quaternion.imJ_coe, Quaternion.imK_coe] <;> norm_num <;> ring

/- Existing original strict derivative and typed scalar-axis/projection API,
   with no added desired derivative, velocity or invertibility premise. -/

end
end Glennie.Compact.NativeFlatColumns89
