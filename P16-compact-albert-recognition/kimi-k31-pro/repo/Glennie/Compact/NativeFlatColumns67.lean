/- Exactly original FlatBase columns6 and7, every Fin20 raw row including zeros.
   Original full-basis11/12 are POSITIVE upper J/K in slot02. Their ordered
   HALF commutators and actual two-index Q/R product projections precede JQ.
   No desired Jacobian/derivative/trace/rank premise or replacement family. -/
module

public import Glennie.Compact.FlatBase
public import Glennie.Compact.Rank20Reduction
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.Calculus.FDeriv.Linear

@[expose] public section

namespace Glennie.Compact.NativeFlatColumns67

open Glennie.Compact.NativeDictionary
open Glennie.Compact.FlatBase
open Glennie.Compact.FlowFamily
open Glennie.Compact.Rank20
open Glennie.Compact.Rank20Certificate

noncomputable section
set_option autoImplicit false

set_option maxHeartbeats 1000000 in
private theorem direction_six_flatFrameP (i : Fin 3) :
    direction 6 (flatFrameP i) =
      ![(⟨0, 0, 0, 0,
          ((⟨0, 0, 1 / 4, 0⟩ : Quaternion ℝ), 0), 0⟩ : Glennie.Albert),
        0,
        ⟨0, 0, 0, 0,
          ((⟨0, 0, -1 / 4, 0⟩ : Quaternion ℝ), 0), 0⟩] i := by
  have hp : partnerIndex (6 : Fin 20) = 11 := rfl
  rw [direction, hp, extDecode_extUnit_1, extDecode_extUnit_11,
    Glennie.Compact.innerDerLinear_apply, flatFrameP_literal i]
  fin_cases i <;> ext <;> flat_coordinate_norm

set_option maxHeartbeats 1000000 in
private theorem direction_seven_flatFrameP (i : Fin 3) :
    direction 7 (flatFrameP i) =
      ![(⟨0, 0, 0, 0,
          ((⟨0, 0, 0, 1 / 4⟩ : Quaternion ℝ), 0), 0⟩ : Glennie.Albert),
        0,
        ⟨0, 0, 0, 0,
          ((⟨0, 0, 0, -1 / 4⟩ : Quaternion ℝ), 0), 0⟩] i := by
  have hp : partnerIndex (7 : Fin 20) = 12 := rfl
  rw [direction, hp, extDecode_extUnit_1, extDecode_extUnit_12,
    Glennie.Compact.innerDerLinear_apply, flatFrameP_literal i]
  fin_cases i <;> ext <;> flat_coordinate_norm

/- Whole actual Q/R literals are rederived from their projector definitions.
   No earlier private helper or assumed coordinate/value table is imported. -/
private theorem flat_pair_o02_imJ (j k : Fin 3) :
    (jordan (flatFrameQ j) (flatFrameR k)).o02.1.imJ =
      ![![flatScale / 12, -flatScale / 12, (0 : ℝ)],
        ![-flatScale / 12, 0, flatScale / 12],
        ![0, flatScale / 12, -flatScale / 12]] j k := by
  rw [flatFrameQ_literal j, flatFrameR_literal k]
  fin_cases j <;> fin_cases k <;>
    norm_num [jordan_o02, octMul,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul] <;> ring

private theorem flat_pair_o02_imK (j k : Fin 3) :
    (jordan (flatFrameQ j) (flatFrameR k)).o02.1.imK =
      ![![(-1 / 36 : ℝ), -1 / 36, 1 / 18],
        ![-1 / 36, 1 / 18, -1 / 36],
        ![1 / 18, -1 / 36, -1 / 36]] j k := by
  rw [flatFrameQ_literal j, flatFrameR_literal k]
  fin_cases j <;> fin_cases k <;>
    norm_num [jordan_o02, octMul,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul] <;>
    ring_nf <;> norm_num [flatScale_sq]

set_option maxHeartbeats 1000000 in
/-- All20 original raw rows of column6, including its twelve zeros. -/
theorem jacobianEntry_flatBase_column_six (r : Fin 20) :
    jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r 6 = JQ r 6 := by
  rw [jacobianEntry_ctx0 _ r 6 (by rfl)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [direction_six_flatFrameP]
  fin_cases r <;>
    norm_num [rowIndex, inner_coordinates, octDot_coordinates,
      flat_pair_o02_imJ, flatScale_eq_sqrt3_div_three, JQ, JZ] <;>
    simp -failIfUnchanged only [← Quaternion.coe_inv, Quaternion.re_coe, Quaternion.imI_coe,
      Quaternion.imJ_coe, Quaternion.imK_coe] <;> norm_num <;> ring

set_option maxHeartbeats 1000000 in
/-- All20 original raw rows of column7, including its eight zeros. -/
theorem jacobianEntry_flatBase_column_seven (r : Fin 20) :
    jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r 7 = JQ r 7 := by
  rw [jacobianEntry_ctx0 _ r 7 (by rfl)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [direction_seven_flatFrameP]
  fin_cases r <;>
    norm_num [rowIndex, inner_coordinates, octDot_coordinates,
      flat_pair_o02_imK, JQ, JZ] <;>
    simp -failIfUnchanged only [← Quaternion.coe_inv, Quaternion.re_coe, Quaternion.imI_coe,
      Quaternion.imJ_coe, Quaternion.imK_coe] <;> norm_num <;> ring

/- Existing original strict derivative and typed scalar-axis/projection API,
   with no added desired derivative, velocity or invertibility premise. -/

end
end Glennie.Compact.NativeFlatColumns67
