/- Exactly original FlatBase columns4 and5, every Fin20 raw row including zeros.
   Full-basis9/10 decode to negative upper J/K in slot12; native HALF ordered
   commutators and actual projector coordinates precede JQ comparison.
   No desired derivative/Jacobian/trace/rank premise or replacement family. -/
module

public import Glennie.Compact.FlatBase
public import Glennie.Compact.Rank20Reduction
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.Calculus.FDeriv.Linear

public import Glennie.Compact.NativeFlatCommon

@[expose] public section

namespace Glennie.Compact.NativeFlatColumns45

open Glennie.Compact.NativeFlatCommon
open Glennie.Compact.NativeDictionary
open Glennie.Compact.FlatBase
open Glennie.Compact.FlowFamily
open Glennie.Compact.Rank20
open Glennie.Compact.Rank20Certificate

noncomputable section

set_option maxHeartbeats 1000000 in
private theorem direction_four_flatFrameP (i : Fin 3) :
    direction 4 (flatFrameP i) =
      ![(⟨0, 0, 0, 0, 0,
          ((⟨0, 0, 1 / 4, 0⟩ : Quaternion ℝ), 0)⟩ : Glennie.Albert),
        ⟨0, 0, 0, 0, 0,
          ((⟨0, 0, -1 / 4, 0⟩ : Quaternion ℝ), 0)⟩,
        0] i := by
  have hp : partnerIndex (4 : Fin 20) = 9 := rfl
  rw [direction, hp, extDecode_extUnit_1, extDecode_extUnit_9,
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
private theorem direction_five_flatFrameP (i : Fin 3) :
    direction 5 (flatFrameP i) =
      ![(⟨0, 0, 0, 0, 0,
          ((⟨0, 0, 0, 1 / 4⟩ : Quaternion ℝ), 0)⟩ : Glennie.Albert),
        ⟨0, 0, 0, 0, 0,
          ((⟨0, 0, 0, -1 / 4⟩ : Quaternion ℝ), 0)⟩,
        0] i := by
  have hp : partnerIndex (5 : Fin 20) = 10 := rfl
  rw [direction, hp, extDecode_extUnit_1, extDecode_extUnit_10,
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

/- Private whole Q/R identities have no public API in the earlier modules.
   Their same literal projector proofs are restated, with the canonical native
   carrier explicit. No previous module, value table or certificate is a premise. -/
private theorem flat_pair_o12_imJ (j k : Fin 3) :
    (jordan (flatFrameQ j) (flatFrameR k)).o12.1.imJ =
      ![(-1 / 18 : ℝ), 1 / 9, -1 / 18] k := by
  rw [flatFrameQ_literal j, flatFrameR_literal k]
  fin_cases j <;> fin_cases k <;>
    norm_num [jordan_o12, octMul, octConj,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul] <;> ring

private theorem flat_pair_o12_imK (j k : Fin 3) :
    (jordan (flatFrameQ j) (flatFrameR k)).o12.1.imK =
      ![flatScale / 6, 0, -flatScale / 6] k := by
  rw [flatFrameQ_literal j, flatFrameR_literal k]
  fin_cases j <;> fin_cases k <;>
    norm_num [jordan_o12, octMul, octConj,
      Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul] <;> ring

theorem jacobianEntry_flatBase_column_four (r : Fin 20) :
    jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r 4 = JQ r 4 := by
  rw [jacobianEntry_ctx0 _ r 4 (by rfl)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [direction_four_flatFrameP]
  fin_cases r <;>
    norm_num [rowIndex, inner_coordinates, octDot_coordinates,
      flat_pair_o12_imJ, JQ, JZ] <;>
    simp -failIfUnchanged only [← Quaternion.coe_inv, Quaternion.re_coe, Quaternion.imI_coe,
      Quaternion.imJ_coe, Quaternion.imK_coe] <;> norm_num <;> ring

set_option maxHeartbeats 1000000 in
/-- Every original raw row of column5, including its ten zeros. -/
theorem jacobianEntry_flatBase_column_five (r : Fin 20) :
    jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r 5 = JQ r 5 := by
  rw [jacobianEntry_ctx0 _ r 5 (by rfl)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [direction_five_flatFrameP]
  fin_cases r <;>
    norm_num [rowIndex, inner_coordinates, octDot_coordinates,
      flat_pair_o12_imK, flatScale_eq_sqrt3_div_three, JQ, JZ] <;>
    simp -failIfUnchanged only [← Quaternion.coe_inv, Quaternion.re_coe, Quaternion.imI_coe,
      Quaternion.imJ_coe, Quaternion.imK_coe] <;> norm_num <;> ring

/- Same existing original strict derivative and typed scalar-axis/projection
   chain rule; no supplied derivative value or invertibility hypothesis. -/

end
end Glennie.Compact.NativeFlatColumns45
