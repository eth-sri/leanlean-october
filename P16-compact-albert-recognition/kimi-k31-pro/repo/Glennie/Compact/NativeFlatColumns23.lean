/- Fixed original FlatBase columns2 and3, each with all20 raw rows including
   zeros. Native projector/CD/HALF coordinate bodies precede comparison with
   JQ; no desired Jacobian hypothesis or replacement family is supplied.
   The literal base below is definitionally Sections.flatBase. Importing
   Sections solely for that alias would add its separate IFT/reversal chain. -/
module

public import Glennie.Compact.FlatBase
public import Glennie.Compact.Rank20Reduction
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.Calculus.FDeriv.Linear

@[expose] public section

namespace Glennie.Compact.NativeFlatColumns23

open Glennie.Compact.NativeDictionary
open Glennie.Compact.FlatBase
open Glennie.Compact.FlowFamily
open Glennie.Compact.Rank20
open Glennie.Compact.Rank20Certificate

noncomputable section
set_option autoImplicit false

set_option maxHeartbeats 1000000 in
private theorem direction_two_flatFrameP (i : Fin 3) :
    direction 2 (flatFrameP i) =
      ![(⟨0, 0, 0, 0, octScalar (1 / 4), 0⟩ : Albert),
        0, ⟨0, 0, 0, 0, octScalar (-1 / 4), 0⟩] i := by
  have hp : partnerIndex (2 : Fin 20) = 5 := rfl
  rw [direction, hp, extDecode_extUnit_1, extDecode_extUnit_5,
    Glennie.Compact.innerDerLinear_apply, flatFrameP_literal i]
  fin_cases i <;> ext <;> flat_coordinate_norm

set_option maxHeartbeats 1000000 in
private theorem direction_three_flatFrameP (i : Fin 3) :
    direction 3 (flatFrameP i) =
      ![(⟨0, 0, 0, 0, ((⟨0, 1 / 4, 0, 0⟩ : Quaternion ℝ), 0), 0⟩ : Albert),
        0, ⟨0, 0, 0, 0, ((⟨0, -1 / 4, 0, 0⟩ : Quaternion ℝ), 0), 0⟩] i := by
  have hp : partnerIndex (3 : Fin 20) = 6 := rfl
  rw [direction, hp, extDecode_extUnit_1, extDecode_extUnit_6,
    Glennie.Compact.innerDerLinear_apply, flatFrameP_literal i]
  fin_cases i <;> ext <;> flat_coordinate_norm

/- These are whole native atom equalities, derived from the projector formula.
   They contain no certificate entry, assumed velocity or trace hypothesis. -/
private theorem flat_pair_o02_re (j k : Fin 3) :
    (jordan (flatFrameQ j) (flatFrameR k)).o02.1.re =
      ![(1 / 18 : ℝ), -1 / 9, 1 / 18] j := by
  rw [flatFrameQ_literal j, flatFrameR_literal k]
  fin_cases j <;> fin_cases k <;>
    norm_num [jordan_o02, octMul,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul] <;> ring

private theorem flat_pair_o02_imI (j k : Fin 3) :
    (jordan (flatFrameQ j) (flatFrameR k)).o02.1.imI =
      ![flatScale / 6, 0, -flatScale / 6] j := by
  rw [flatFrameQ_literal j, flatFrameR_literal k]
  fin_cases j <;> fin_cases k <;>
    norm_num [jordan_o02, octMul,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul] <;> ring

set_option maxHeartbeats 1000000 in
/-- All20 original raw rows in fixed column2, including its eight zeros.
    The literal triple is exactly the original Sections.flatBase. -/
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
      Quaternion.imJ_coe, Quaternion.imK_coe] <;> norm_num <;> ring

set_option maxHeartbeats 1000000 in
/-- All20 original raw rows in fixed column3, including its thirteen zeros.
    The scalar conversion uses the actual positive-root definition of flatScale. -/
theorem jacobianEntry_flatBase_column_three (r : Fin 20) :
    jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r 3 = JQ r 3 := by
  rw [jacobianEntry_ctx0 _ r 3 (by rfl)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [direction_three_flatFrameP]
  fin_cases r <;>
    norm_num [rowIndex, inner_coordinates, octDot_coordinates,
      flat_pair_o02_imI, flatScale_eq_sqrt3_div_three, JQ, JZ] <;> ring

/- This internal chain rule adds no derivative equality hypothesis. It fixes
   the same original triple and consumes its written strict family derivative. -/

end
end Glennie.Compact.NativeFlatColumns23
