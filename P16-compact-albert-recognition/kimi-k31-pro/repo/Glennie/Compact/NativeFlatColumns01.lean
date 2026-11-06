/- Exactly original FlatBase columns0 and1, all20 rows including zeros.
   Their native coordinate proofs precede comparison with JQ. The
   NativeFlatColumns23 module supplies only the two original fixed-column
   comparisons used by the final four-column conjunction. This module adds
   no desired derivative/Jacobian hypothesis, replacement family or definition. -/
module

public import Glennie.Compact.NativeFlatColumns23

@[expose] public section

namespace Glennie.Compact.NativeFlatColumns01

open Glennie.Compact.NativeDictionary
open Glennie.Compact.FlatBase
open Glennie.Compact.FlowFamily
open Glennie.Compact.Rank20
open Glennie.Compact.Rank20Certificate

noncomputable section
set_option autoImplicit false

set_option maxHeartbeats 1000000 in
private theorem direction_zero_flatFrameP (i : Fin 3) :
    direction 0 (flatFrameP i) =
      ![(0 : Albert),
        ⟨0, 0, 0, octScalar (1 / 2), 0, 0⟩,
        ⟨0, 0, 0, octScalar (-1 / 2), 0, 0⟩] i := by
  have hp : partnerIndex (0 : Fin 20) = 3 := rfl
  rw [direction, hp, extDecode_extUnit_1, extDecode_extUnit_3,
    Glennie.Compact.innerDerLinear_apply, flatFrameP_literal i]
  fin_cases i <;> ext <;> flat_coordinate_norm

set_option maxHeartbeats 1000000 in
private theorem direction_one_flatFrameP (i : Fin 3) :
    direction 1 (flatFrameP i) =
      ![(0 : Albert),
        ⟨0, 0, 0, ((⟨0, 1 / 2, 0, 0⟩ : Quaternion ℝ), 0), 0, 0⟩,
        ⟨0, 0, 0, ((⟨0, -1 / 2, 0, 0⟩ : Quaternion ℝ), 0), 0, 0⟩] i := by
  have hp : partnerIndex (1 : Fin 20) = 4 := rfl
  rw [direction, hp, extDecode_extUnit_1, extDecode_extUnit_4,
    Glennie.Compact.innerDerLinear_apply, flatFrameP_literal i]
  fin_cases i <;> ext <;> flat_coordinate_norm

/- These are whole native atom equalities, derived from the projector formula.
   They contain no certificate entry, assumed velocity or trace hypothesis. -/
private theorem flat_pair_o01_re (j k : Fin 3) :
    (jordan (flatFrameQ j) (flatFrameR k)).o01.1.re =
      ![-flatScale / 6, 0, flatScale / 6] j := by
  rw [flatFrameQ_literal j, flatFrameR_literal k]
  fin_cases j <;> fin_cases k <;>
    norm_num [jordan_o01, octMul, octConj,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul] <;> ring

private theorem flat_pair_o01_imI (j k : Fin 3) :
    (jordan (flatFrameQ j) (flatFrameR k)).o01.1.imI =
      ![(-1 / 18 : ℝ), 1 / 9, -1 / 18] j := by
  rw [flatFrameQ_literal j, flatFrameR_literal k]
  fin_cases j <;> fin_cases k <;>
    norm_num [jordan_o01, octMul, octConj,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul] <;> ring

set_option maxHeartbeats 1000000 in
/-- All20 original raw rows in fixed column0, including its thirteen zeros. -/
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

set_option maxHeartbeats 1000000 in
/-- All20 original raw rows in fixed column1, including its eight zeros. -/
theorem jacobianEntry_flatBase_column_one (r : Fin 20) :
    jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r 1 = JQ r 1 := by
  rw [jacobianEntry_ctx0 _ r 1 (by rfl)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [direction_one_flatFrameP]
  fin_cases r <;>
    norm_num [rowIndex, inner_coordinates, octDot_coordinates,
      flat_pair_o01_imI, JQ, JZ] <;>
    simp only [← Quaternion.coe_inv, Quaternion.re_coe, Quaternion.imI_coe,
      Quaternion.imJ_coe, Quaternion.imK_coe] <;> norm_num <;> ring

/- This internal chain rule adds no derivative equality hypothesis. It fixes
   the same original triple and consumes its written strict family derivative. -/

end
end Glennie.Compact.NativeFlatColumns01
