/- Exactly original FlatBase columns16/17, all Fin20 raw rows including zeros.
   Actual basis11/12 are POSITIVE upper J/K in slot02; BOTH contexts are1.
   Whole Q tangents have upper J/K slots01 and12; P/R atom tangents vanish
   only at these actual context1 axes. Native HALF and all20 movements retained.
   No desired Jacobian/derivative/trace/rank premise or replacement family. -/
module

public import Glennie.Compact.FlatBase
public import Glennie.Compact.Rank20Reduction
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.Calculus.FDeriv.Linear

@[expose] public section

namespace Glennie.Compact.NativeFlatColumns1617

open Glennie.Compact.NativeDictionary
open Glennie.Compact.FlatBase
open Glennie.Compact.FlowFamily
open Glennie.Compact.Rank20
open Glennie.Compact.Rank20Certificate

noncomputable section
set_option autoImplicit false

/- Whole actual Q/R literals are rederived from their projector definitions.
   No earlier private helper or assumed coordinate/value table is imported. -/
set_option maxHeartbeats 1000000 in
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
  have hp : partnerIndex (16 : Fin 20) = 11 := rfl
  rw [direction, hp, extDecode_extUnit_1, extDecode_extUnit_11,
    Glennie.Compact.innerDerLinear_apply, flatFrameQ_literal j]
  fin_cases j <;> ext <;> flat_coordinate_norm <;> ring

set_option maxHeartbeats 1000000 in
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
  have hp : partnerIndex (17 : Fin 20) = 12 := rfl
  rw [direction, hp, extDecode_extUnit_1, extDecode_extUnit_12,
    Glennie.Compact.innerDerLinear_apply, flatFrameQ_literal j]
  fin_cases j <;> ext <;> flat_coordinate_norm <;> ring

/- All nine P/R slot01 upper quaternions are zero. Both native mixed
   words vanish because P has no off-diagonal coordinates, not by a CD swap. -/
private theorem flat_pair_o01_upper_zero (i k : Fin 3) :
    (jordan (flatFrameP i) (flatFrameR k)).o01.1 = 0 := by
  rw [flatFrameP_literal i, flatFrameR_literal k]
  fin_cases i <;> fin_cases k <;> ext <;>
    norm_num [diagonalAlbert, jordan_o01, octMul, octConj,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul]

/- All nine whole P/R slot12 upper quaternions: both J/K projections
   are retained, including the whole zero i2 row. -/
private theorem flat_pair_o12_upper_JK (i k : Fin 3) :
    (jordan (flatFrameP i) (flatFrameR k)).o12.1 =
      ![![(⟨0, 0, -1 / 12, flatScale / 4⟩ : Quaternion ℝ),
          ⟨0, 0, 1 / 6, 0⟩, ⟨0, 0, -1 / 12, -flatScale / 4⟩],
        ![⟨0, 0, -1 / 12, flatScale / 4⟩,
          ⟨0, 0, 1 / 6, 0⟩, ⟨0, 0, -1 / 12, -flatScale / 4⟩],
        ![0, 0, 0]] i k := by
  rw [flatFrameP_literal i, flatFrameR_literal k]
  fin_cases i <;> fin_cases k <;> ext <;>
    norm_num [diagonalAlbert, jordan_o12, octMul, octConj,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul] <;> ring

set_option maxHeartbeats 1000000 in
/-- All20 original raw rows of column16, including its ten zeros. -/
theorem jacobianEntry_flatBase_column_sixteen (r : Fin 20) :
    jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r 16 = JQ r 16 := by
  rw [jacobianEntry_ctx1 _ r 16 (by rfl)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [direction_sixteen_flatFrameQ]
  fin_cases r <;>
    norm_num [rowIndex, inner_coordinates, octDot_coordinates,
      flat_pair_o01_upper_zero, flat_pair_o12_upper_JK,
      flatScale_eq_sqrt3_div_three, JQ, JZ] <;>
    simp -failIfUnchanged only [← Quaternion.coe_inv, Quaternion.re_coe, Quaternion.imI_coe,
      Quaternion.imJ_coe, Quaternion.imK_coe] <;> norm_num <;> ring

set_option maxHeartbeats 1000000 in
/-- All20 original raw rows of column17, including its four zeros. -/
theorem jacobianEntry_flatBase_column_seventeen (r : Fin 20) :
    jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r 17 = JQ r 17 := by
  rw [jacobianEntry_ctx1 _ r 17 (by rfl)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [direction_seventeen_flatFrameQ]
  fin_cases r <;>
    norm_num [rowIndex, inner_coordinates, octDot_coordinates,
      flat_pair_o01_upper_zero, flat_pair_o12_upper_JK, JQ, JZ] <;>
    ring_nf <;> norm_num [flatScale_sq] <;>
    simp -failIfUnchanged only [← Quaternion.coe_inv, Quaternion.re_coe, Quaternion.imI_coe,
      Quaternion.imJ_coe, Quaternion.imK_coe] <;> norm_num

/- Existing original strict derivative and typed scalar-axis/projection API,
   with no added desired derivative, velocity or invertibility premise. -/

end
end Glennie.Compact.NativeFlatColumns1617
