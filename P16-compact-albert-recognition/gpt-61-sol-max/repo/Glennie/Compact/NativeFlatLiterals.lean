/- Shared native projector coordinates for the flat-Jacobian columns. -/
module
public import Glennie.Native.CoordinateSimp
public import Glennie.Compact.FlatBase
public import Glennie.Compact.Rank20Reduction
public import Mathlib.Tactic.NormNum

@[expose] public section
namespace Glennie.Compact.NativeFlatLiterals
open Glennie.Compact.NativeDictionary Glennie.Compact.FlatBase
  Glennie.Compact.FlowFamily Glennie.Compact.Rank20Certificate
noncomputable section

theorem flatScale_eq_sqrt3_div_three : flatScale = Real.sqrt 3 / 3 := (Real.sqrt_div_self' (x := (3 : ℝ))).symm

/-- Polynomial normalization after the finite row and atom cases are split. -/
macro "flat_scalar" "[" ds:term,* "]" : tactic =>
  `(tactic| (norm_num [inner_coordinates, octDot_coordinates, rowIndex, JQ, J0, columnScale,
      $[$ds:term],*] <;>
    (try simp only [← Quaternion.coe_inv, Quaternion.re_coe,
      Quaternion.imI_coe, Quaternion.imJ_coe, Quaternion.imK_coe]) <;>
    norm_num <;> ring_nf <;> norm_num [flatScale_sq]))

/-- Expand the Albert product before scalar normalization. -/
macro "flat_coordinates" "[" ds:term,* "]" : tactic =>
  `(tactic| (flat_scalar [Glennie.Compact.innerDer, diagonalAlbert, complexAlbert,
    complexOct, hiddenAlbert, hiddenOct, jordan_d0, jordan_d1,
    jordan_d2, jordan_o01, jordan_o02, jordan_o12, octNormSq,
    Quaternion.normSq_def', octMul, octConj, octScalar, Quaternion.re_mul,
    Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, $[$ds:term],*]))

/-- Compute a column directly, using the literal frames and the bilinear product. -/
macro "flat_column" r:ident n:term : tactic =>
  `(tactic| ((first
      | rw [Glennie.Compact.Rank20.jacobianEntry_ctx0 _ $r $n rfl]
      | rw [Glennie.Compact.Rank20.jacobianEntry_ctx1 _ $r $n rfl]) <;>
    fin_cases $r:ident <;>
      flat_coordinates [direction, partnerIndex, extDecode, extDecode0, extUnit, extTail,
        Glennie.Compact.innerDerLinear_apply, flatFrameP_literal, flatFrameQ_literal,
        flatFrameR_literal, flatScale_eq_sqrt3_div_three]))

/-- Certify a four-column batch, keeping the expensive coordinate computations in
separate modules while sharing their common statement and proof. -/
macro "flat_block " nm:ident b:num : command =>
  `(set_option maxHeartbeats 0 in
    set_option maxRecDepth 10000 in
    public theorem $nm (r : Fin 20) (n : Fin 4) :
        jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r ⟨$b + n.val, by omega⟩ =
          JQ r ⟨$b + n.val, by omega⟩ := by
      fin_cases n <;> flat_column r _)

end
end Glennie.Compact.NativeFlatLiterals
