/- Exactly original FlatBase columns10 and11, all Fin20 raw rows including zeros.
   Actual basis15/16 are NEGATIVE lower quaternion1/I in slot12, contexts0/0.
   Ordered native HALF commutators give (+1/4,-1/4,0); both conjugated slot12
   mixed words and lower re/I projections precede final original JQ comparison.
   No desired Jacobian/derivative/trace/rank premise or replacement family. -/
module

public import Glennie.Compact.FlatBase
public import Glennie.Compact.Rank20Reduction
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.Calculus.FDeriv.Linear

public import Glennie.Compact.NativeFlatCommon

@[expose] public section

namespace Glennie.Compact.NativeFlatColumns1011

open Glennie.Compact.NativeFlatCommon
open Glennie.Compact.NativeDictionary
open Glennie.Compact.FlatBase
open Glennie.Compact.FlowFamily
open Glennie.Compact.Rank20
open Glennie.Compact.Rank20Certificate

noncomputable section

set_option maxHeartbeats 1000000 in
private theorem direction_ten_flatFrameP (i : Fin 3) :
    direction 10 (flatFrameP i) =
      ![(⟨0, 0, 0, 0, 0,
          (0, (⟨1 / 4, 0, 0, 0⟩ : Quaternion ℝ))⟩ : Glennie.Albert),
        ⟨0, 0, 0, 0, 0,
          (0, (⟨-1 / 4, 0, 0, 0⟩ : Quaternion ℝ))⟩,
        0] i := by
  have hp : partnerIndex (10 : Fin 20) = 15 := rfl
  rw [direction, hp, extDecode_extUnit_1, extDecode_extUnit_15,
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
private theorem direction_eleven_flatFrameP (i : Fin 3) :
    direction 11 (flatFrameP i) =
      ![(⟨0, 0, 0, 0, 0,
          (0, (⟨0, 1 / 4, 0, 0⟩ : Quaternion ℝ))⟩ : Glennie.Albert),
        ⟨0, 0, 0, 0, 0,
          (0, (⟨0, -1 / 4, 0, 0⟩ : Quaternion ℝ))⟩,
        0] i := by
  have hp : partnerIndex (11 : Fin 20) = 16 := rfl
  rw [direction, hp, extDecode_extUnit_1, extDecode_extUnit_16,
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
private theorem flat_pair_o12_lower_re (j k : Fin 3) :
    (jordan (flatFrameQ j) (flatFrameR k)).o12.2.re =
      ![![(-1 / 18 : ℝ), 1 / 36, 1 / 36],
        ![1 / 36, -1 / 18, 1 / 36],
        ![1 / 36, 1 / 36, -1 / 18]] j k := by
  rw [flatFrameQ_literal j, flatFrameR_literal k]
  fin_cases j <;> fin_cases k <;>
    norm_num [jordan_o12, octMul, octConj,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul] <;>
    ring_nf <;> norm_num [flatScale_sq]

private theorem flat_pair_o12_lower_imI (j k : Fin 3) :
    (jordan (flatFrameQ j) (flatFrameR k)).o12.2.imI =
      ![![(0 : ℝ), flatScale / 12, -flatScale / 12],
        ![-flatScale / 12, 0, flatScale / 12],
        ![flatScale / 12, -flatScale / 12, 0]] j k := by
  rw [flatFrameQ_literal j, flatFrameR_literal k]
  fin_cases j <;> fin_cases k <;>
    norm_num [jordan_o12, octMul, octConj,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul] <;> ring

theorem jacobianEntry_flatBase_column_ten (r : Fin 20) :
    jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r 10 = JQ r 10 := by
  rw [jacobianEntry_ctx0 _ r 10 (by rfl)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [direction_ten_flatFrameP]
  fin_cases r <;>
    norm_num [rowIndex, inner_coordinates, octDot_coordinates,
      flat_pair_o12_lower_re, JQ, JZ] <;>
    simp -failIfUnchanged only [← Quaternion.coe_inv, Quaternion.re_coe, Quaternion.imI_coe,
      Quaternion.imJ_coe, Quaternion.imK_coe] <;> norm_num <;> ring

set_option maxHeartbeats 1000000 in
/-- All20 original raw rows of column11, including its eight zeros. -/
theorem jacobianEntry_flatBase_column_eleven (r : Fin 20) :
    jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r 11 = JQ r 11 := by
  rw [jacobianEntry_ctx0 _ r 11 (by rfl)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [direction_eleven_flatFrameP]
  fin_cases r <;>
    norm_num [rowIndex, inner_coordinates, octDot_coordinates,
      flat_pair_o12_lower_imI, flatScale_eq_sqrt3_div_three, JQ, JZ] <;>
    simp -failIfUnchanged only [← Quaternion.coe_inv, Quaternion.re_coe, Quaternion.imI_coe,
      Quaternion.imJ_coe, Quaternion.imK_coe] <;> norm_num <;> ring

/- Existing original strict derivative and typed scalar-axis/projection API,
   with no added desired derivative, velocity or invertibility premise. -/

end
end Glennie.Compact.NativeFlatColumns1011
