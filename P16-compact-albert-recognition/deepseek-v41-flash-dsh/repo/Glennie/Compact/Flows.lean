/- For a real-linear D on Albert that obeys the Leibniz law
(`IsJordanDerivation`) and is trace-free (`TraceFree`), the exponential flow
exp(t D) is a genuine `CompactAutomorphism` for every real t.
  * Product preservation is derived, not assumed. For fixed a, b the curve
    s |-> exp(-sD) (exp(sD) a o exp(sD) b) has derivative 0 by the Leibniz law,
    so it is constant (mean value theorem, `is_const_of_deriv_eq_zero`).
  * Trace preservation is derived the same way from trace-freeness.
  * Invertibility: exp(tD) exp(t(-D)) = 1 = exp(t(-D)) exp(tD) (`exp_add_of_commute`).
  * The unit is fixed automatically (`CompactAutomorphism.map_unit`).
Albert has no norm instance, so the exponential lives in the Banach algebra
of continuous linear maps of the coordinate space Fin 27 -> R, transported by
the dictionary equivalence `extEquiv`. The family
D = sum_i c_i [L_{a_i}, L_{b_i}] (`innerSpan`) gives `innerFlowAut`. -/
module

public import Glennie.Compact.InnerDerivation
public import Glennie.Compact.NativeDictionary
public import Glennie.Automorphism
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

namespace Glennie.Compact.Flows

open Glennie.Compact.NativeDictionary

noncomputable section

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-! ## Coordinate transport -/

/-- A real-linear map of Albert read on the coordinate space, as a continuous linear map. -/
def toCoord (D : Albert →ₗ[ℝ] Albert) : (Fin 27 → ℝ) →L[ℝ] (Fin 27 → ℝ) :=
  LinearMap.toContinuousLinearMap
    (extEquiv.symm.toLinearMap ∘ₗ D ∘ₗ extEquiv.toLinearMap)

theorem toCoord_apply (D : Albert →ₗ[ℝ] Albert) (a : Fin 27 → ℝ) :
    toCoord D a = extEquiv.symm (D (extEquiv a)) := rfl

/-- The native product read on coordinates, as a continuous bilinear map. -/
def prodC : (Fin 27 → ℝ) →L[ℝ] (Fin 27 → ℝ) →L[ℝ] (Fin 27 → ℝ) :=
  LinearMap.toContinuousLinearMap
    (LinearMap.toContinuousLinearMap.toLinearMap.comp
      ((jordanLinear.compl₁₂ extEquiv.toLinearMap extEquiv.toLinearMap).compr₂
        extEquiv.symm.toLinearMap))

theorem prodC_apply (a b : Fin 27 → ℝ) :
    prodC a b = extEquiv.symm (jordan (extEquiv a) (extEquiv b)) := rfl

theorem prodC_symm (x y : Albert) :
    prodC (extEquiv.symm x) (extEquiv.symm y) = extEquiv.symm (jordan x y) := by
  simp only [prodC_apply, LinearEquiv.apply_symm_apply]

/-- The raw trace read on coordinates, as a continuous functional. -/
def traceC : (Fin 27 → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (traceLinear ∘ₗ extEquiv.toLinearMap)

theorem traceC_apply (a : Fin 27 → ℝ) : traceC a = trace (extEquiv a) := rfl
variable (D : Albert →ₗ[ℝ] Albert)
include D in

/-- The Leibniz law, transported to coordinates. -/
theorem toCoord_prodC  (hD : IsJordanDerivation D)
    (a b : Fin 27 → ℝ) :
    toCoord D (prodC a b) = prodC (toCoord D a) b + prodC a (toCoord D b) := by
  have h := hD (extEquiv a) (extEquiv b)
  simp only [toCoord_apply, prodC_apply, LinearEquiv.apply_symm_apply, h, map_add]
include D in

/-! ## The flow and its inverse -/

/-- exp(t D) on coordinates. -/
def flowC  (t : ℝ) : (Fin 27 → ℝ) →L[ℝ] (Fin 27 → ℝ) :=
  NormedSpace.exp (t • toCoord D)
include D in

/-- exp(t (-D)) on coordinates: the inverse flow. -/
def flowInvC  (t : ℝ) : (Fin 27 → ℝ) →L[ℝ] (Fin 27 → ℝ) :=
  NormedSpace.exp (t • -toCoord D)
include D in

theorem flowC_zero  : flowC D 0 = 1 := by
  simp [flowC]
include D in

theorem flowInvC_zero  : flowInvC D 0 = 1 := by
  simp [flowInvC]
include D in

theorem flowC_mul_flowInvC  (t : ℝ) :
    flowC D t * flowInvC D t = 1 := by
  let +nondep : NormedAlgebra ℚ ((Fin 27 → ℝ) →L[ℝ] (Fin 27 → ℝ)) :=
    .restrictScalars ℚ ℝ _
  have h : Commute (t • toCoord D) (t • -toCoord D) :=
    (((Commute.refl (toCoord D)).neg_right).smul_left t).smul_right t
  rw [flowC, flowInvC, ← NormedSpace.exp_add_of_commute h, ← smul_add, add_neg_cancel,
    smul_zero, NormedSpace.exp_zero]
include D in

theorem flowInvC_mul_flowC  (t : ℝ) :
    flowInvC D t * flowC D t = 1 := by
  let +nondep : NormedAlgebra ℚ ((Fin 27 → ℝ) →L[ℝ] (Fin 27 → ℝ)) :=
    .restrictScalars ℚ ℝ _
  have h : Commute (t • -toCoord D) (t • toCoord D) :=
    (((Commute.refl (toCoord D)).neg_left).smul_left t).smul_right t
  rw [flowC, flowInvC, ← NormedSpace.exp_add_of_commute h, ← smul_add, neg_add_cancel,
    smul_zero, NormedSpace.exp_zero]
include D in

theorem flowC_flowInvC_apply  (t : ℝ) (c : Fin 27 → ℝ) :
    flowC D t (flowInvC D t c) = c := by
  rw [← mul_apply_eq_comp, flowC_mul_flowInvC, one_apply_eq_self]
include D in

theorem flowInvC_flowC_apply  (t : ℝ) (c : Fin 27 → ℝ) :
    flowInvC D t (flowC D t c) = c := by
  rw [← mul_apply_eq_comp, flowInvC_mul_flowC, one_apply_eq_self]
include D in

/-! ## Derivatives -/

theorem hasDerivAt_flowC_apply  (c : Fin 27 → ℝ) (t : ℝ) :
    HasDerivAt (fun s => flowC D s c) (toCoord D (flowC D t c)) t := by
  have h : HasDerivAt (fun s => flowC D s c) ((toCoord D * flowC D t) c + flowC D t 0) t :=
    (hasDerivAt_exp_smul_const' (toCoord D) t).clm_apply (hasDerivAt_const t c)
  refine h.congr_deriv ?_
  rw [mul_apply_eq_comp, map_zero, add_zero]
include D in

theorem hasDerivAt_flowInvC  (t : ℝ) :
    HasDerivAt (fun s => flowInvC D s) (flowInvC D t * -toCoord D) t := by
  simpa [flowInvC] using hasDerivAt_exp_smul_const (-toCoord D) t
include D in

/-! ## Product and trace preservation -/

/-- exp(t D) preserves the native product, for every derivation D. -/
theorem flowC_prodC  (hD : IsJordanDerivation D)
    (a b : Fin 27 → ℝ) (t : ℝ) :
    flowC D t (prodC a b) = prodC (flowC D t a) (flowC D t b) := by
  have hderiv : ∀ s : ℝ, HasDerivAt
      (fun r => flowInvC D r (prodC (flowC D r a) (flowC D r b))) 0 s := by
    intro s
    have hu := hasDerivAt_flowC_apply D a s
    have hv := hasDerivAt_flowC_apply D b s
    have hpu : HasDerivAt (fun r => prodC (flowC D r a))
        (prodC (toCoord D (flowC D s a))) s :=
      prodC.hasFDerivAt.comp_hasDerivAt s hu
    have hw : HasDerivAt (fun r => prodC (flowC D r a) (flowC D r b))
        (prodC (toCoord D (flowC D s a)) (flowC D s b) +
          prodC (flowC D s a) (toCoord D (flowC D s b))) s :=
      hpu.clm_apply hv
    have hall : HasDerivAt (fun r => flowInvC D r (prodC (flowC D r a) (flowC D r b)))
        ((flowInvC D s * -toCoord D) (prodC (flowC D s a) (flowC D s b)) +
          flowInvC D s (prodC (toCoord D (flowC D s a)) (flowC D s b) +
            prodC (flowC D s a) (toCoord D (flowC D s b)))) s :=
      (hasDerivAt_flowInvC D s).clm_apply hw
    refine hall.congr_deriv ?_
    rw [mul_apply_eq_comp, neg_apply, ← map_add, ← toCoord_prodC D hD, neg_add_cancel,
      map_zero]
  have hconst := is_const_of_deriv_eq_zero
    (fun s => (hderiv s).differentiableAt) (fun s => (hderiv s).deriv) t 0
  simp only [flowC_zero, flowInvC_zero, one_apply_eq_self] at hconst
  have h2 := congrArg (flowC D t) hconst
  rw [flowC_flowInvC_apply] at h2
  exact h2.symm
include D in

/-- exp(t D) preserves the raw trace, for every trace-free D. -/
theorem flowC_traceC  (hT : TraceFree D)
    (a : Fin 27 → ℝ) (t : ℝ) :
    traceC (flowC D t a) = traceC a := by
  have hderiv : ∀ s : ℝ, HasDerivAt (fun r => traceC (flowC D r a)) 0 s := by
    intro s
    have h : HasDerivAt (fun r => traceC (flowC D r a)) (traceC (toCoord D (flowC D s a))) s :=
      traceC.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_flowC_apply D a s)
    refine h.congr_deriv ?_
    rw [traceC_apply, toCoord_apply, LinearEquiv.apply_symm_apply,
      hT (extEquiv (flowC D s a))]
  have hconst := is_const_of_deriv_eq_zero
    (fun s => (hderiv s).differentiableAt) (fun s => (hderiv s).deriv) t 0
  simpa only [flowC_zero, one_apply_eq_self] using hconst
include D in

/-! ## The flow on Albert as a compact automorphism -/

def flowL  (t : ℝ) : Albert →ₗ[ℝ] Albert :=
  extEquiv.toLinearMap ∘ₗ (flowC D t : (Fin 27 → ℝ) →ₗ[ℝ] (Fin 27 → ℝ)) ∘ₗ
    extEquiv.symm.toLinearMap
include D in

def flowInvL  (t : ℝ) : Albert →ₗ[ℝ] Albert :=
  extEquiv.toLinearMap ∘ₗ (flowInvC D t : (Fin 27 → ℝ) →ₗ[ℝ] (Fin 27 → ℝ)) ∘ₗ
    extEquiv.symm.toLinearMap
include D in

/-- The flow exp(t D) as a real-linear equivalence of Albert. -/
def flow  (t : ℝ) : Albert ≃ₗ[ℝ] Albert :=
  LinearEquiv.ofLinearMap (flowL D t) (flowInvL D t)
    (LinearMap.ext fun x => by
      simp [flowL, flowInvL, flowC_flowInvC_apply])
    (LinearMap.ext fun x => by
      simp [flowL, flowInvL, flowInvC_flowC_apply])
include D in

theorem flow_apply  (t : ℝ) (x : Albert) :
    flow D t x = extEquiv (flowC D t (extEquiv.symm x)) := rfl
include D in

theorem flow_jordan  (hD : IsJordanDerivation D) (t : ℝ)
    (x y : Albert) : flow D t (jordan x y) = jordan (flow D t x) (flow D t y) := by
  simp only [flow_apply]
  rw [← prodC_symm, flowC_prodC D hD, prodC_apply, LinearEquiv.apply_symm_apply]
include D in

theorem flow_trace  (hT : TraceFree D) (t : ℝ) (x : Albert) :
    trace (flow D t x) = trace x := by
  have h := flowC_traceC D hT (extEquiv.symm x) t
  simp only [traceC_apply, LinearEquiv.apply_symm_apply] at h
  rw [flow_apply]
  exact h
include D in

/-- Step 3 headline: exp(t D) is a genuine compact automorphism (product and
trace preserving real-linear equivalence) for every derivation D that is
trace-free. -/
def flowAut  (hD : IsJordanDerivation D) (hT : TraceFree D)
    (t : ℝ) : CompactAutomorphism where
  equiv := flow D t
  map_jordan := flow_jordan D hD t
  map_trace := flow_trace D hT t
include D in

theorem flowAut_apply  (hD : IsJordanDerivation D)
    (hT : TraceFree D) (t : ℝ) (x : Albert) :
    (flowAut D hD hT t).equiv x = flow D t x := rfl

/-! ## Flows of real combinations of inner derivations -/

end
end Glennie.Compact.Flows
