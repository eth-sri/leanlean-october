/- The C^1 family and its derivative formula.
  * For directions D_1 .. D_k (Jordan derivations, trace-free) and parameters
    s in R^k, `familyAut D s` is the compact automorphism exp(sum_n s_n D_n)
    (`flowAut` at time 1). On the native Hilbert space this is
    `familyC D s = exp (spanC D s)`, and s |-> familyC D s has strict
    Frechet derivative `spanC D` at s = 0 (exp has strict derivative 1 at 0).
    It is continuous in s everywhere.
  * Each frame a of a triple T is moved by its own direction family D a. Every
    ledger entry of the moved triple is a map of s with strict Frechet derivative
    at 0; its value in direction h is
      T((D0(h) T0i o T1j) o T2l) + T((T0i o D1(h) T1j) o T2l) + T((T0i o T1j) o D2(h) T2l)
    with Da(h) = sum_n h_n D_{a,n}.
  * Specialization: twenty directions [L_t, L_b] with t = basis 1 and
    b = basis (partnerIndex n), read through the dictionary
    (`extDecode (extUnit m)` gives the basis vectors), sixteen on the
    first frame and four on the second. The twenty selected rows have strict
    derivative at 0 whose (r, n) entry is the `jacobianEntry`
    (`rowLedgerDeriv_single`). This holds for every triple T; the flat base is one instance. No rank or determinant claim is made here. -/
module

public import Glennie.Compact.Flows
public import Glennie.Compact.NativeDictionaryLiteral
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

@[expose] public section

namespace Glennie.Compact.FlowFamily

open Glennie.Compact.NativeDictionary Glennie.Compact.Flows

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance 20000] nativeRealSMulComm nativeRealContinuousAdd nativeRealContinuousSMul
real_operator_norms familyDualNorm familyDualSpace Albert ℝ
real_operator_norms familyEndNorm familyEndSpace Albert Albert
attribute [local instance] nativeEndTopologicalRing

variable {k : ℕ}
section Families
variable (D : Fin k → Albert →ₗ[ℝ] Albert)

/-! ## The parameter-to-generator map -/

/-- s |-> sum_n s_n D_n, realized continuously, as a continuous linear map. -/
def spanC :
    (Fin k → ℝ) →L[ℝ] (Albert →L[ℝ] Albert) :=
  ∑ n, (ContinuousLinearMap.proj n : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (derivC (D n))

theorem spanC_apply (s : Fin k → ℝ) :
    spanC D s = ∑ n, s n • derivC (D n) := by
  simp only [spanC, sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply]

/-- The real-linear combination sum_n s_n D_n on Albert. -/
def spanDer (s : Fin k → ℝ) :
    Albert →ₗ[ℝ] Albert :=
  ∑ n, s n • D n

theorem spanDer_apply (s : Fin k → ℝ)
    (x : Albert) : spanDer D s x = ∑ n, s n • D n x := by
  simp only [spanDer, LinearMap.sum_apply, LinearMap.smul_apply]

theorem derivC_spanDer (s : Fin k → ℝ) :
    derivC (spanDer D s) = spanC D s := by
  refine ContinuousLinearMap.ext fun a => ?_
  simp only [derivC_apply, spanDer_apply, spanC_apply, sum_apply,
    smul_apply]

theorem spanDer_single (n : Fin k) (x : Albert) :
    spanDer D (Pi.single n 1) x = D n x := by
  simp [spanDer_apply, Pi.single_apply]

theorem spanDer_isJordanDerivation {D : Fin k → Albert →ₗ[ℝ] Albert}
    (hD : ∀ n, IsJordanDerivation (D n)) (s : Fin k → ℝ) :
    IsJordanDerivation (spanDer D s) :=
  IsJordanDerivation.sum Finset.univ (fun n => s n • D n) (fun n _ => (hD n).smul (s n))

theorem spanDer_traceFree {D : Fin k → Albert →ₗ[ℝ] Albert}
    (hT : ∀ n, TraceFree (D n)) (s : Fin k → ℝ) : TraceFree (spanDer D s) :=
  TraceFree.sum Finset.univ (fun n => s n • D n) (fun n _ => (hT n).smul (s n))

/-! ## The family exp(sum_n s_n D_n) -/

/-- exp(sum_n s_n D_n) on the native Hilbert space. -/
def familyC (s : Fin k → ℝ) :
    Albert →L[ℝ] Albert :=
  NormedSpace.exp (spanC D s)

theorem flowC_spanDer (s : Fin k → ℝ) :
    flowC (spanDer D s) 1 = familyC D s := by
  rw [flowC, one_smul, derivC_spanDer, familyC]

theorem familyC_zero_apply (v : Albert) :
    familyC D 0 v = v := by
  rw [familyC, map_zero, NormedSpace.exp_zero, one_apply_eq_self]

/-- The family has strict Frechet derivative `spanC D` at s = 0. -/
theorem hasStrictFDerivAt_familyC :
    HasStrictFDerivAt (familyC D) (spanC D) 0 := by
  have h := hasStrictFDerivAt_exp_zero (𝕂 := ℝ)
    (𝔸 := Albert →L[ℝ] Albert)
  rw [← map_zero (spanC D)] at h
  refine (h.comp (0 : Fin k → ℝ) (spanC D).hasStrictFDerivAt).congr_fderiv ?_
  rfl

theorem hasStrictFDerivAt_familyC_apply
    (v : Albert) :
    HasStrictFDerivAt (fun s => familyC D s v) ((spanC D).flip v) 0 :=
  (ContinuousLinearMap.apply ℝ Albert v).hasStrictFDerivAt.comp 0
    (hasStrictFDerivAt_familyC D)

/-- Every atom varies continuously with the parameters. -/
theorem continuous_familyC_apply
    (v : Albert) : Continuous fun s => familyC D s v := by
  let +nondep : NormedAlgebra ℚ (Albert →L[ℝ] Albert) :=
    .restrictScalars ℚ ℝ _
  exact (NormedSpace.exp_continuous.comp (spanC D).continuous).clm_apply continuous_const

/-! ## The family as compact automorphisms -/

/-- exp(sum_n s_n D_n) as a compact automorphism (flowAut at time 1). -/
def familyAut
    (hD : ∀ n, IsJordanDerivation (D n)) (hT : ∀ n, TraceFree (D n)) (s : Fin k → ℝ) :
    CompactAutomorphism :=
  flowAut (spanDer D s) (spanDer_isJordanDerivation hD s) (spanDer_traceFree hT s) 1

theorem familyAut_apply
    (hD : ∀ n, IsJordanDerivation (D n)) (hT : ∀ n, TraceFree (D n)) (s : Fin k → ℝ)
    (x : Albert) :
    (familyAut D hD hT s).equiv x = familyC D s x := by
  rw [familyAut, flowAut_apply, flowC_spanDer]

end Families

/-! ## Moved frames -/

/-- Frame a of the triple T, moved by the family automorphism of its own directions D a. -/
def movedFrame (D : Fin 3 → Fin k → Albert →ₗ[ℝ] Albert)
    (hD : ∀ a n, IsJordanDerivation (D a n)) (hT : ∀ a n, TraceFree (D a n))
    (T : Fin 3 → Fin 3 → Albert) (a : Fin 3) (s : Fin k → ℝ) : Fin 3 → Albert :=
  fun i => (familyAut (D a) (hD a) (hT a) s).equiv (T a i)

variable (D : Fin 3 → Fin k → Albert →ₗ[ℝ] Albert)
    (hD : ∀ a n, IsJordanDerivation (D a n)) (hT : ∀ a n, TraceFree (D a n))
    (T : Fin 3 → Fin 3 → Albert)

theorem movedFrame_frame  (a : Fin 3) (hF : Frame (T a)) (s : Fin k → ℝ) :
    Frame (movedFrame D hD hT T a s) :=
  (familyAut (D a) (hD a) (hT a) s).map_frame (T a) hF

include k D hD hT T in
theorem movedFrame_zero  (a : Fin 3) : movedFrame D hD hT T a 0 = T a := by
  funext i
  simp only [movedFrame, familyAut_apply, familyC_zero_apply]

/-- Every moved atom depends continuously on the parameters. -/
theorem continuous_movedFrame (a i : Fin 3) :
    Continuous fun s : Fin k → ℝ => movedFrame D hD hT T a s i := by
  simp only [movedFrame, familyAut_apply]
  exact continuous_familyC_apply (D a) _

/-! ## Ledger entries and their strict derivative -/

private theorem pairing_apply (x y : Albert) : nativeInnerContinuous x y = inner x y := rfl

def movedLedgerDeriv (D : Fin 3 → Fin k → Albert →ₗ[ℝ] Albert)
    (T : Fin 3 → Fin 3 → Albert) (i j l : Fin 3) : (Fin k → ℝ) →L[ℝ] ℝ :=
  (nativeInnerContinuous (jordanContinuous (T 0 i) (T 1 j))).comp ((spanC (D 2)).flip (T 2 l)) +
    (nativeInnerContinuous.comp
      ((jordanContinuous (T 0 i)).comp ((spanC (D 1)).flip (T 1 j)) +
        (jordanContinuous.comp ((spanC (D 0)).flip (T 0 i))).flip (T 1 j))).flip (T 2 l)

/-! ## The twenty directions, read through the dictionary -/

/-- The partner full27 indices, in the minor-column order. -/
def partnerIndex : Fin 20 → Fin 27 :=
  ![3, 4, 5, 6, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20,
    11, 12, 13, 14]

/-- Sixteen first-frame and four second-frame directions; none third-frame. -/
def contextIndex (n : Fin 20) : Fin 3 := if n.val < 16 then 0 else 1

/-- The twenty selected ordered triple-ledger rows. -/
def rowIndex (r : Fin 20) : Fin 3 × Fin 3 × Fin 3 :=
  let d : ℕ := if r.val < 16 then 3 else 2
  (⟨r.val / 8, by omega⟩,
   ⟨r.val % 8 / d, by dsimp [d]; split_ifs <;> omega⟩,
   ⟨r.val % 8 % d, by dsimp [d]; split_ifs <;> omega⟩)

/-- [L_t, L_b] with t = basis 1 and b = basis (partnerIndex n), halved native product,
no factor 4. Basis vectors are `extDecode (extUnit m)`. -/
def direction (n : Fin 20) : Albert →ₗ[ℝ] Albert :=
  innerDerLinear (extDecode (extUnit 1)) (extDecode (extUnit (partnerIndex n)))

/-- The direction family of frame a: direction n if it belongs to frame a, else 0. -/
def contextDirection (a : Fin 3) (n : Fin 20) : Albert →ₗ[ℝ] Albert :=
  if a = contextIndex n then direction n else 0

theorem contextDirection_isJordanDerivation (a : Fin 3) (n : Fin 20) :
    IsJordanDerivation (contextDirection a n) := by
  unfold contextDirection
  split_ifs
  · exact isJordanDerivation_innerDerLinear _ _
  · exact IsJordanDerivation.zero

theorem contextDirection_traceFree (a : Fin 3) (n : Fin 20) :
    TraceFree (contextDirection a n) := by
  unfold contextDirection
  split_ifs
  · exact traceFree_innerDerLinear _ _
  · exact TraceFree.zero

theorem contextDirection_apply (a : Fin 3) (n : Fin 20) (x : Albert) :
    contextDirection a n x = if a = contextIndex n then direction n x else 0 := by
  unfold contextDirection
  split_ifs <;> rfl

/-- The atom tangent. -/
def atomTangent (T : Fin 3 → Fin 3 → Albert) (n : Fin 20) (a i : Fin 3) : Albert :=
  if a = contextIndex n then direction n (T a i) else 0

/-- The literal scalar `jacobianEntry`, with its `let`s inlined. -/
def jacobianEntry (T : Fin 3 → Fin 3 → Albert) (r n : Fin 20) : ℝ :=
  trace (jordan (jordan (atomTangent T n 0 (rowIndex r).1) (T 1 (rowIndex r).2.1))
      (T 2 (rowIndex r).2.2) +
    jordan (jordan (T 0 (rowIndex r).1) (atomTangent T n 1 (rowIndex r).2.1))
      (T 2 (rowIndex r).2.2) +
    jordan (jordan (T 0 (rowIndex r).1) (T 1 (rowIndex r).2.1))
      (atomTangent T n 2 (rowIndex r).2.2))

/-- The twenty selected ledger rows of the moved triple, as a map of s in R^20. -/
def rowLedger (T : Fin 3 → Fin 3 → Albert) (s : Fin 20 → ℝ) : Fin 20 → ℝ := fun r =>
  ledger (movedFrame contextDirection contextDirection_isJordanDerivation
      contextDirection_traceFree T 0 s)
    (movedFrame contextDirection contextDirection_isJordanDerivation
      contextDirection_traceFree T 1 s)
    (movedFrame contextDirection contextDirection_isJordanDerivation
      contextDirection_traceFree T 2 s)
    (rowIndex r).1 (rowIndex r).2.1 (rowIndex r).2.2

/-- Its strict derivative at 0, row by row. -/
def rowLedgerDeriv (T : Fin 3 → Fin 3 → Albert) : (Fin 20 → ℝ) →L[ℝ] (Fin 20 → ℝ) :=
  ContinuousLinearMap.pi fun r =>
    movedLedgerDeriv contextDirection T (rowIndex r).1 (rowIndex r).2.1 (rowIndex r).2.2

theorem hasStrictFDerivAt_rowLedger (T : Fin 3 → Fin 3 → Albert) :
    HasStrictFDerivAt (rowLedger T) (rowLedgerDeriv T) 0 := by
  refine hasStrictFDerivAt_pi'.2 fun r => ?_
  have hd := (nativeInnerContinuous.hasStrictFDerivAt.comp 0
    ((jordanContinuous.hasStrictFDerivAt.comp 0
      (hasStrictFDerivAt_familyC_apply (contextDirection 0) (T 0 (rowIndex r).1))).clm_apply
      (hasStrictFDerivAt_familyC_apply (contextDirection 1) (T 1 (rowIndex r).2.1)))).clm_apply
      (hasStrictFDerivAt_familyC_apply (contextDirection 2) (T 2 (rowIndex r).2.2))
  simpa only [rowLedger, rowLedgerDeriv, ContinuousLinearMap.proj_pi, familyC_zero_apply, ledger, movedFrame, familyAut_apply,
    jordanContinuous_apply_apply, pairing_apply, inner, movedLedgerDeriv] using hd

theorem rowLedgerDeriv_single (T : Fin 3 → Fin 3 → Albert) (r n : Fin 20) :
    rowLedgerDeriv T (Pi.single n 1) r = jacobianEntry T r n := by
  simp only [rowLedgerDeriv, ContinuousLinearMap.pi_apply, movedLedgerDeriv,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, add_apply, map_add,
    ← derivC_spanDer, derivC_apply, jordanContinuous_apply_apply, pairing_apply, inner,
    spanDer_single, contextDirection_apply, atomTangent, jacobianEntry, trace_add]
  ring

end
end Glennie.Compact.FlowFamily
