/- Exactly original FlatBase columns12 and13, all Fin20 raw rows including zeros.
   Actual basis17/18 are POSITIVE lower quaternion1/I in slot02, contexts0/0.
   Ordered native HALF commutators give (+1/4,0,-1/4); both unconjugated slot02
   mixed words and lower re/I projections precede final original JQ comparison.
   No desired Jacobian/derivative/trace/rank premise or replacement family. -/
module

public import Glennie.Compact.FlatBase
public import Glennie.Compact.Rank20Reduction
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.Calculus.FDeriv.Linear

@[expose] public section

namespace Glennie.Compact.NativeFlatColumns1213

open Glennie.Compact.NativeDictionary
open Glennie.Compact.FlatBase
open Glennie.Compact.FlowFamily
open Glennie.Compact.Rank20
open Glennie.Compact.Rank20Certificate

noncomputable section
set_option autoImplicit false

set_option maxHeartbeats 1000000 in
private theorem direction_twelve_flatFrameP (i : Fin 3) :
    direction 12 (flatFrameP i) =
      ![(⟨0, 0, 0, 0,
          (0, (⟨1 / 4, 0, 0, 0⟩ : Quaternion ℝ)), 0⟩ : Glennie.Albert),
        0,
        ⟨0, 0, 0, 0,
          (0, (⟨-1 / 4, 0, 0, 0⟩ : Quaternion ℝ)), 0⟩] i := by
  have hp : partnerIndex (12 : Fin 20) = 17 := rfl
  rw [direction, hp, extDecode_extUnit_1, extDecode_extUnit_17,
    Glennie.Compact.innerDerLinear_apply, flatFrameP_literal i]
  fin_cases i <;> ext <;> flat_coordinate_norm

set_option maxHeartbeats 1000000 in
private theorem direction_thirteen_flatFrameP (i : Fin 3) :
    direction 13 (flatFrameP i) =
      ![(⟨0, 0, 0, 0,
          (0, (⟨0, 1 / 4, 0, 0⟩ : Quaternion ℝ)), 0⟩ : Glennie.Albert),
        0,
        ⟨0, 0, 0, 0,
          (0, (⟨0, -1 / 4, 0, 0⟩ : Quaternion ℝ)), 0⟩] i := by
  have hp : partnerIndex (13 : Fin 20) = 18 := rfl
  rw [direction, hp, extDecode_extUnit_1, extDecode_extUnit_18,
    Glennie.Compact.innerDerLinear_apply, flatFrameP_literal i]
  fin_cases i <;> ext <;> flat_coordinate_norm

/- Whole actual Q/R literals are rederived from their projector definitions.
   No earlier private helper or assumed coordinate/value table is imported. -/
/- Actual slot02 mixed words are Q01*R12 and R01*Q12, with no outer
   conjugation. The first is upper quaternion; the second has lower part
   w*star(A), pure lower J/K. The lower re/I cut is the R02 diagonal term. -/
private theorem flat_pair_o02_lower_re (j k : Fin 3) :
    (jordan (flatFrameQ j) (flatFrameR k)).o02.2.re =
      ![(flatScale / 6 : ℝ), 0, -flatScale / 6] k := by
  rw [flatFrameQ_literal j, flatFrameR_literal k]
  fin_cases j <;> fin_cases k <;>
    norm_num [jordan_o02, octMul,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul] <;> ring

private theorem flat_pair_o02_lower_imI (j k : Fin 3) :
    (jordan (flatFrameQ j) (flatFrameR k)).o02.2.imI =
      ![(1 / 18 : ℝ), -1 / 9, 1 / 18] k := by
  rw [flatFrameQ_literal j, flatFrameR_literal k]
  fin_cases j <;> fin_cases k <;>
    norm_num [jordan_o02, octMul,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul] <;> ring

set_option maxHeartbeats 1000000 in
/-- All20 original raw rows of column12, including its thirteen zeros. -/
theorem jacobianEntry_flatBase_column_twelve (r : Fin 20) :
    jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r 12 = JQ r 12 := by
  rw [jacobianEntry_ctx0 _ r 12 (by rfl)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [direction_twelve_flatFrameP]
  fin_cases r <;>
    norm_num [rowIndex, inner_coordinates, octDot_coordinates,
      flat_pair_o02_lower_re, flatScale_eq_sqrt3_div_three, JQ, JZ] <;>
    simp -failIfUnchanged only [← Quaternion.coe_inv, Quaternion.re_coe, Quaternion.imI_coe,
      Quaternion.imJ_coe, Quaternion.imK_coe] <;> norm_num <;> ring

set_option maxHeartbeats 1000000 in
/-- All20 original raw rows of column13, including its eight zeros. -/
theorem jacobianEntry_flatBase_column_thirteen (r : Fin 20) :
    jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r 13 = JQ r 13 := by
  rw [jacobianEntry_ctx0 _ r 13 (by rfl)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [direction_thirteen_flatFrameP]
  fin_cases r <;>
    norm_num [rowIndex, inner_coordinates, octDot_coordinates,
      flat_pair_o02_lower_imI, JQ, JZ] <;>
    simp -failIfUnchanged only [← Quaternion.coe_inv, Quaternion.re_coe, Quaternion.imI_coe,
      Quaternion.imJ_coe, Quaternion.imK_coe] <;> norm_num <;> ring

/- Existing original strict derivative and typed scalar-axis/projection API,
   with no added desired derivative, velocity or invertibility premise. -/

end
end Glennie.Compact.NativeFlatColumns1213
