module

public import PDEFoundation.Sobolev.W1p.ConvexApprox.WeakDerivSmoothing
public import PDEFoundation.Calculus.RegularityOrder


/-!
# Continuity of convex-domain smoothing

This file closes the weak-derivative smoothing chain by identifying the
classical coordinate derivatives of the smooth representative almost
everywhere. It also records the elementary continuity, support, and
integrability facts used by pointwise bounds and `L^p` convergence.

The separate classical-input differentiation-under-the-integral theory is not
part of this foundational module.
-/

 public section

open scoped Pointwise Convolution

namespace PDE

/-- The classical coordinate derivative of the smooth representative agrees
almost everywhere with the correspondingly smoothed weak derivative, including
the exact affine factor `1 - ε`. -/
theorem ae_eq_fderiv_convexApproxSmoothRepresentative_apply_basisVec
    {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U)
    {i : Fin d} {u gi ρ : Vec d → ℝ} {p : ENNReal}
    (hρ : IsConvexApproxKernel ρ) (hp : 1 ≤ p)
    (huMem : MemLpOn U p u) (hgiMem : MemLpOn U p gi)
    (huWeak : HasWeakPartialDerivOn U i u gi)
    {x0 : Vec d} {r ε : ℝ}
    (hball : Metric.closedBall x0 r ⊆ U)
    (hr : 0 < r) (hε : 0 < ε) (hεOne : ε < 1) :
    (fun x =>
        (fderiv ℝ
          (convexApproxSmoothRepresentative U ρ u x0 r ε) x)
          (basisVec i)) =ᵐ[MeasureTheory.volume.restrict U]
      fun x =>
        (1 - ε) *
          convexApproxSmoothRepresentative U ρ gi x0 r ε x := (HasWeakPartialDerivOn.ae_eq (IsOpenBoundedConvexDomain.isOpen hU)
  (ContinuousOn.locallyIntegrableOn
    (Continuous.continuousOn
      (Continuous.clm_apply
        (ContDiff.continuous_fderiv
          (contDiff_convexApproxSmoothRepresentative (IsOpenBoundedConvexDomain.measurableSet hU) hρ hp huMem hr hε)
          (of_eq_true
            (Eq.trans (congrArg Not (Eq.trans WithTop.coe_eq_zero._simp_1 ENat.top_ne_zero._simp_1))
              not_false_eq_true)))
        continuous_const))
    (IsOpenBoundedConvexDomain.measurableSet hU))
  (ContinuousOn.locallyIntegrableOn
    (Continuous.continuousOn
      (Continuous.mul continuous_const
        (ContDiff.continuous
          (contDiff_convexApproxSmoothRepresentative (IsOpenBoundedConvexDomain.measurableSet hU) hρ hp hgiMem hr hε))))
    (IsOpenBoundedConvexDomain.measurableSet hU))
  (HasWeakPartialDerivOn.of_contDiff
    (ContDiff.of_le
      (contDiff_convexApproxSmoothRepresentative (IsOpenBoundedConvexDomain.measurableSet hU) hρ hp huMem hr hε)
      (of_eq_true
        (Eq.trans WithTop.le_coe_top._simp_1 (Eq.trans (congrArg Not WithTop.one_ne_top._simp_2) not_false_eq_true)))))
  (HasWeakPartialDerivOn.convexApproxSmoothRepresentative hU
    (MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict (MeasureTheory.MemLp.locallyIntegrable huMem hp))
    (MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict (MeasureTheory.MemLp.locallyIntegrable hgiMem hp))
    huWeak hρ hball hr hε hεOne))

variable {d : ℕ}

variable (x0 : Vec d) (r ε : ℝ)

theorem continuous_convexApproxSample_right
      (x : Vec d) :
    Continuous
      (fun z  =>
        convexApproxSample x0 z r ε x) := by
  unfold convexApproxSample
  fun_prop

theorem continuous_convexApproxSample_prod
      :
    Continuous
      (fun xz : Vec d × Vec d =>
        convexApproxSample x0 xz.2 r ε xz.1) := by
  unfold convexApproxSample
  fun_prop

variable {ρ u : Vec d → ℝ}

section
variable (hρ : Continuous ρ) (hu : Continuous u) (x0 : Vec d) (r ε : ℝ)

include hρ hu
theorem continuous_convexApproxIntegrand_right

     (x : Vec d) :
    Continuous
      ((convexApproxIntegrand ρ u x0 r ε x)) := (Continuous.mul hρ (Continuous.comp hu (continuous_convexApproxSample_right x0 r ε x)))

theorem continuous_convexApproxIntegrand_prod

     :
    Continuous
      (fun xz : Vec d × Vec d =>
        convexApproxIntegrand
          ρ u x0 r ε xz.1 xz.2) := (id (Continuous.mul (Continuous.comp hρ continuous_snd) (Continuous.comp hu (continuous_convexApproxSample_prod x0 r ε))))
end


theorem hasCompactSupport_convexApproxIntegrand

    (hρ : HasCompactSupport ρ)
    (x0 : Vec d) (r ε : ℝ) (x : Vec d) :
    HasCompactSupport
      ((convexApproxIntegrand ρ u x0 r ε x)) := (HasCompactSupport.mul_right hρ)

theorem integrable_convexApproxIntegrand

    (hρ : Continuous ρ)
    (hρCompact : HasCompactSupport ρ)
    (hu : Continuous u)
    (x0 : Vec d) (r ε : ℝ) (x : Vec d) :
    MeasureTheory.Integrable
      ((convexApproxIntegrand ρ u x0 r ε x)) :=
  (continuous_convexApproxIntegrand_right
      hρ hu x0 r ε x).integrable_of_hasCompactSupport
    (hasCompactSupport_convexApproxIntegrand
      hρCompact x0 r ε x)

theorem continuous_convexApproxWeightedOscillation

    (hρ : Continuous ρ) (hu : Continuous u)
    (x0 : Vec d) (r ε : ℝ) (x : Vec d) :
    Continuous
      (fun z =>
        ρ z *
          |u (convexApproxSample x0 z r ε x) - u x|) :=
  hρ.mul
    (((hu.comp
      (continuous_convexApproxSample_right
        x0 r ε x)).sub continuous_const).abs)

theorem hasCompactSupport_convexApproxWeightedOscillation

    (hρCompact : HasCompactSupport ρ)
    (x0 : Vec d) (r ε : ℝ) (x : Vec d) :
    HasCompactSupport
      (fun z =>
        ρ z *
          |u (convexApproxSample x0 z r ε x) - u x|) := (HasCompactSupport.mul_right hρCompact)

theorem integrable_convexApproxWeightedOscillation

    (hρ : Continuous ρ)
    (hρCompact : HasCompactSupport ρ)
    (hu : Continuous u)
    (x0 : Vec d) (r ε : ℝ) (x : Vec d) :
    MeasureTheory.Integrable
      (fun z =>
        ρ z *
          |u (convexApproxSample x0 z r ε x) - u x|) :=
  (continuous_convexApproxWeightedOscillation
      hρ hu x0 r ε x).integrable_of_hasCompactSupport
    (hasCompactSupport_convexApproxWeightedOscillation
      hρCompact x0 r ε x)

theorem integrable_convexApproxKernelMulConst
     {ρ : Vec d → ℝ}
    (hρ : Continuous ρ)
    (hρCompact : HasCompactSupport ρ)
    (c : ℝ) :
    MeasureTheory.Integrable
      (fun z => ρ z * c) := (Continuous.integrable_of_hasCompactSupport (Continuous.mul hρ continuous_const) (HasCompactSupport.mul_right hρCompact))

theorem continuous_convexApproxSmoothing
     {ρ u : Vec d → ℝ}
    (hρ : Continuous ρ)
    (hρCompact : HasCompactSupport ρ)
    (hu : Continuous u)
    (x0 : Vec d) (r ε : ℝ) :
    Continuous
      (convexApproxSmoothing ρ u x0 r ε) := (continuous_parametric_integral_of_continuous (continuous_convexApproxIntegrand_prod hρ hu x0 r ε)
  (HasCompactSupport.isCompact hρCompact))

end PDE
