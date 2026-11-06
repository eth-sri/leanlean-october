/- For an arbitrary triple T:
  * `toMatrix'_rowLedgerDeriv`: the matrix of the strict derivative
    `rowLedgerDeriv T` in the standard basis is `jacobianEntry T`.
  * `exists_equiv_of_det_ne_zero`: if that matrix has nonzero determinant,
    `rowLedgerDeriv T` is a continuous linear equivalence of R^20, so
    `rowLedger T` has an invertible strict derivative at 0 (the input of the
    inverse function theorem).
  * `jacobianEntry_ctx0/ctx1` and `inner_innerDer_left`: the entry formula reduced
    to one trace pairing, the form the flat-base bridge will evaluate.
  * `rank20_of_bridge`: conditional on the entrywise bridge
    `jacobianEntry T r n = JQ r n` (stated as an explicit hypothesis, not
    assumed anywhere), rank 20 follows from the certificate `det_JQ_ne_zero`. -/
module

public import Glennie.Compact.FlowFamily
public import Glennie.Compact.Rank20Certificate
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

namespace Glennie.Compact.Rank20

open Glennie.Compact.FlowFamily
  Glennie.Compact.Rank20Certificate



/-! ## The derivative matrix and invertibility -/

/-- The twenty rows then have an invertible strict derivative at 0. -/
theorem hasStrictFDerivAt_rowLedger_of_equiv (T : Fin 3 → Fin 3 → Albert)
    (e : (Fin 20 → ℝ) ≃L[ℝ] (Fin 20 → ℝ))
    (he : (e : (Fin 20 → ℝ) →L[ℝ] (Fin 20 → ℝ)) = rowLedgerDeriv T) :
    HasStrictFDerivAt (rowLedger T) (e : (Fin 20 → ℝ) →L[ℝ] (Fin 20 → ℝ)) 0 :=
  he ▸ hasStrictFDerivAt_rowLedger T

/-- Conditional rank 20: if the derivative matrix at T is the certified matrix JQ, the
strict derivative of the twenty rows at T is a continuous linear equivalence. -/
theorem rank20_of_bridge (T : Fin 3 → Fin 3 → Albert)
    (hT : ∀ r n : Fin 20, jacobianEntry T r n = JQ r n) :
    ∃ e : (Fin 20 → ℝ) ≃L[ℝ] (Fin 20 → ℝ),
      (e : (Fin 20 → ℝ) →L[ℝ] (Fin 20 → ℝ)) = rowLedgerDeriv T := by
  have hdet : (rowLedgerDeriv T).det ≠ 0 := by
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix', show LinearMap.toMatrix' _ = JQ by
      ext r n
      rw [LinearMap.toMatrix'_apply, ContinuousLinearMap.coe_coe, rowLedgerDeriv_single, hT]]
    exact det_JQ_ne_zero
  exact ⟨_, (rowLedgerDeriv T).coe_toContinuousLinearEquivOfDetNeZero hdet⟩

end Glennie.Compact.Rank20

set_option hygiene false in
macro "flat_col" : tactic => `(tactic| (
  simp [jacobianEntry, atomTangent, contextIndex, direction, partnerIndex, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue, ↓reduceIte, Fin.reduceEq]
  simp [extDecode_extUnit_1, extDecode_extUnit_3, extDecode_extUnit_4, extDecode_extUnit_5,
    extDecode_extUnit_6, extDecode_extUnit_9, extDecode_extUnit_10, extDecode_extUnit_11,
    extDecode_extUnit_12, extDecode_extUnit_13, extDecode_extUnit_14, extDecode_extUnit_15,
    extDecode_extUnit_16, extDecode_extUnit_17, extDecode_extUnit_18, extDecode_extUnit_19,
    extDecode_extUnit_20, Glennie.Compact.innerDerLinear_apply, LinearMap.zero_apply,
    jordan_zero_left, jordan_zero_right, add_zero, zero_add]
  fin_cases r <;>
  norm_num [rowIndex, trace, inner_coordinates, octDot_coordinates, flatFrameP_literal,
    flatFrameQ_literal, flatFrameR_literal, Glennie.Compact.innerDer, diagonalAlbert,
    complexAlbert, complexOct, archivalHiddenBasis, hiddenAlbert, hiddenOct, oct_simps, JQ, JZ,
    flatScale_eq_sqrt3_div_three] <;>
  simp -failIfUnchanged only [← Quaternion.coe_inv, Quaternion.re_coe, Quaternion.imI_coe,
      Quaternion.imJ_coe, Quaternion.imK_coe] <;> ring_nf <;> norm_num))

set_option hygiene false in
macro "flat_cols" ns:num* : command => do
  let cmds ← ns.mapM fun (n : Lean.NumLit) => `(command| @[simp] theorem $(Lean.mkIdent (.mkSimple s!"col{n.getNat}"))
    (r : Fin 20) : jacobianEntry ![flatFrameP, flatFrameQ, flatFrameR] r $n = JQ r $n := by flat_col)
  return ⟨Lean.mkNullNode cmds⟩
