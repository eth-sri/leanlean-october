/- Native exponential flows of Jordan derivations. Product preservation follows
by differentiating exp(-tD)(exp(tD)a ∘ exp(tD)b); trace follows from trace-freeness. -/
module

public import Glennie.Compact.InnerDerivation
public import Glennie.Compact.NativeDictionary
public import Glennie.Compactness
public import AlbertGeometry.LinearSimp
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

namespace Glennie.Compact.Flows

open Glennie.Compact.NativeDictionary

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
real_operator_norms flowEndNorm flowEndSpace Albert Albert

theorem nativeEndTopologicalRing : IsTopologicalRing (Albert →L[ℝ] Albert) :=
  @NonUnitalSeminormedRing.toIsTopologicalRing (Albert →L[ℝ] Albert) inferInstance
attribute [local instance] nativeEndTopologicalRing

/-- The continuous realization of a native derivation. -/
def derivC (D : Albert →ₗ[ℝ] Albert) :=
  D.toContinuousLinearMap

variable (D : Albert →ₗ[ℝ] Albert)

theorem derivC_apply (a : Albert) : derivC D a = D a := rfl

/-! ## The flow and its inverse -/

/-- exp(t D) on the native Hilbert space. -/
def flowC (D : Albert →ₗ[ℝ] Albert) (t : ℝ) : Albert →L[ℝ] Albert :=
  NormedSpace.exp (t • derivC D)

/-- exp(t (-D)) on the native Hilbert space: the inverse flow. -/
def flowInvC (D : Albert →ₗ[ℝ] Albert) (t : ℝ) : Albert →L[ℝ] Albert :=
  NormedSpace.exp (t • -derivC D)

theorem flowC_zero  : flowC D 0 = 1 := by
  simp [flowC]

theorem flowInvC_zero  : flowInvC D 0 = 1 := by
  simp [flowInvC]

theorem flowC_mul_flowInvC  (t : ℝ) :
    flowC D t * flowInvC D t = 1 := by
  let +nondep : NormedAlgebra ℚ (Albert →L[ℝ] Albert) :=
    .restrictScalars ℚ ℝ _
  simpa only [flowC, flowInvC, smul_neg, NormedSpace.invertibleExp,
    NormedSpace.invertibleExpOfMemBall, Invertible.invOf] using
    (NormedSpace.invertibleExp (t • derivC D)).mul_invOf_self

theorem flowInvC_mul_flowC  (t : ℝ) :
    flowInvC D t * flowC D t = 1 := by
  convert flowC_mul_flowInvC D (-t) using 2 <;>
    unfold flowC flowInvC <;> congr 1 <;> module

theorem flowC_flowInvC_apply  (t : ℝ) (c : Albert) :
    flowC D t (flowInvC D t c) = c := by
  rw [← mul_apply_eq_comp, flowC_mul_flowInvC, one_apply_eq_self]

theorem flowInvC_flowC_apply  (t : ℝ) (c : Albert) :
    flowInvC D t (flowC D t c) = c := by
  rw [← mul_apply_eq_comp, flowInvC_mul_flowC, one_apply_eq_self]

/-! ## Derivatives -/

theorem hasDerivAt_flowC_apply  (c : Albert) (t : ℝ) :
    HasDerivAt (fun s => flowC D s c) (derivC D (flowC D t c)) t := by
  have h :=
    (hasDerivAt_exp_smul_const' (derivC D) t).clm_apply (hasDerivAt_const t c)
  simpa only [flowC, mul_apply_eq_comp, map_zero, add_zero] using h

/-! ## Product and trace preservation -/

/-- exp(t D) preserves the native product, for every derivation D. -/
theorem flowC_prodC  (hD : IsJordanDerivation D)
    (a b : Albert) (t : ℝ) :
    flowC D t (jordanContinuous a b) = jordanContinuous (flowC D t a) (flowC D t b) := by
  have hderiv : ∀ s : ℝ, HasDerivAt
      (fun r => flowInvC D r (jordanContinuous (flowC D r a) (flowC D r b))) 0 s := by
    intro s
    have hu := hasDerivAt_flowC_apply D a s
    have hv := hasDerivAt_flowC_apply D b s
    have hw := (jordanContinuous.hasFDerivAt.comp_hasDerivAt s hu).clm_apply hv
    have hall := (hasDerivAt_exp_smul_const (-derivC D) s).clm_apply hw
    refine hall.congr_deriv ?_
    rw [mul_apply_eq_comp, neg_apply, ← map_add]
    simp only [Function.comp_apply, derivC_apply, jordanContinuous_apply_apply, ← hD _ _, neg_add_cancel, map_zero]
  have hconst := is_const_of_deriv_eq_zero
    (fun s => (hderiv s).differentiableAt) (fun s => (hderiv s).deriv) t 0
  simp only [flowC_zero, flowInvC_zero, one_apply_eq_self] at hconst
  have h2 := congrArg (flowC D t) hconst
  rw [flowC_flowInvC_apply] at h2
  exact h2.symm

/-- exp(t D) preserves the raw trace, for every trace-free D. -/
theorem flowC_traceC  (hT : TraceFree D)
    (a : Albert) (t : ℝ) :
    trace (flowC D t a) = trace a := by
  have hderiv : ∀ s : ℝ, HasDerivAt (fun r => trace (flowC D r a)) 0 s := by
    intro s
    have h :=
      traceLinear.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_flowC_apply D a s)
    refine h.congr_deriv ?_
    exact hT (flowC D s a)
  have hconst := is_const_of_deriv_eq_zero
    (fun s => (hderiv s).differentiableAt) (fun s => (hderiv s).deriv) t 0
  simpa only [flowC_zero, one_apply_eq_self] using hconst

/-! ## The flow on Albert as a compact automorphism -/

/-- The native exponential is an actual product-and-trace-preserving equivalence. -/
def flowAut (D : Albert →ₗ[ℝ] Albert) (hD : IsJordanDerivation D) (hT : TraceFree D)
    (t : ℝ) : CompactAutomorphism where
  equiv := LinearEquiv.ofLinearMap (flowC D t).toLinearMap (flowInvC D t).toLinearMap
    (LinearMap.ext (flowC_flowInvC_apply D t))
    (LinearMap.ext (flowInvC_flowC_apply D t))
  map_jordan x y := flowC_prodC D hD x y t
  map_trace x := flowC_traceC D hT x t

theorem flowAut_apply (hD : IsJordanDerivation D) (hT : TraceFree D)
    (t : ℝ) (x : Albert) : (flowAut D hD hT t).equiv x = flowC D t x := rfl

end
end Glennie.Compact.Flows
