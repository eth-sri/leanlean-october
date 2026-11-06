module

public import Mathlib.Analysis.Normed.Operator.Extend
public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientSmoothCore
public import HypoellipticAleksandrov.Parabolic.Dirichlet.SmoothH10DenseRange

/-!
# Localized spatial quotients on spatial `H¹₀`

This module extends the bounded localized quotient on actual smooth tests to
the complete zero-boundary Sobolev graph.  It records only fixed-step spatial
preservation and its quotient-level value and gradient components.
-/

@[expose] public section

noncomputable section

open scoped ENNReal

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

private theorem exists_localizedSpatialDifferenceQuotientSmoothCore_bound
    {d : ℕ} {Ω inner outer : PDE.VelocityRegion d} {K : ℝ}
    (hΩ : IsOpen Ω)
    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo
      (fun y  => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    ∃ C : ℝ, ∀ φ : PDE.WeakTestFunction Ω,
      ‖localizedSpatialDifferenceQuotientSmoothCoreLinearMap
          hΩ η k h hηΩ φ‖ ≤ C *
        ‖smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ‖ := (Exists.intro (2 * (1 + ↑d * (K + 1)) / |h|) fun φ =>
  norm_localizedSpatialDifferenceQuotientSmoothCoreLinearMap_apply_le hΩ η k h φ hηΩ hηshift)

set_option linter.unusedVariables false in
section
variable {d : ℕ} {Ω inner outer : PDE.VelocityRegion d} {K : ℝ} (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K) (k : Fin d) (h : ℝ)

/-- The localized spatial quotient extended from the actual smooth core to
the complete zero-boundary Sobolev graph. The forward collar fixes the
regime in which the advertised core agreement and norm bound hold. -/
@[nolint unusedArguments]
def localizedSpatialDifferenceQuotientH10CLM

    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo
      (fun y  => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
  (localizedSpatialDifferenceQuotientSmoothCoreLinearMap
    hΩ η k h hηΩ).extendOfNorm
      (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ)

/-- The extended quotient agrees with the literal bounded map on every
actual bundled smooth test. -/
theorem localizedSpatialDifferenceQuotientH10CLM_apply_smooth
     (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo
      (fun y  => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    localizedSpatialDifferenceQuotientH10CLM
        hΩ η k h hηΩ hηshift
        (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ) =
      localizedSpatialDifferenceQuotientSmoothCoreLinearMap
        hΩ η k h hηΩ φ := by
  unfold localizedSpatialDifferenceQuotientH10CLM
  exact LinearMap.extendOfNorm_eq
    (denseRange_smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ)
    (exists_localizedSpatialDifferenceQuotientSmoothCore_bound
      hΩ η k h hηΩ hηshift) φ

variable (hηΩ : tsupport η.toFun ⊆ Ω) (hηshift : Set.MapsTo (fun y : PDE.Vec d => y + h • PDE.basisVec k) (tsupport η.toFun) Ω)

/-- The value component of the extended quotient is exactly the
quotient-level scalar operator. -/
theorem valueCLM_comp_localizedSpatialDifferenceQuotientH10CLM

     :
    (valueCLM hΩ).comp
        (localizedSpatialDifferenceQuotientH10CLM
          hΩ η k h hηΩ hηshift) =
      (localizedSpatialDifferenceQuotientL2
        hΩ.measurableSet η k h).comp (valueCLM hΩ) := (id
  (ContinuousLinearMap.ext fun x =>
    congrFun
      (DenseRange.equalizer (denseRange_smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ)
        (ContinuousLinearMap.continuous (valueCLM hΩ ∘SL localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift))
        (ContinuousLinearMap.continuous
          (localizedSpatialDifferenceQuotientL2 (IsOpen.measurableSet hΩ) η k h ∘SL valueCLM hΩ))
        (funext fun φ =>
          id
            (id
              (Eq.mpr
                (id
                  (congrArg
                    (fun _a =>
                      (valueCLM hΩ) _a =
                        (localizedSpatialDifferenceQuotientL2 (IsOpen.measurableSet hΩ) η k h)
                          ((valueCLM hΩ) ((smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ) φ)))
                    (localizedSpatialDifferenceQuotientH10CLM_apply_smooth hΩ η k h φ hηΩ hηshift)))
                (valueCLM_localizedSpatialDifferenceQuotientSmoothCoreLinearMap_apply hΩ η k h φ hηΩ hηshift)))))
      x))

/-- The gradient component of the extended quotient is exactly the
assembled quotient-level vector operator. -/
theorem gradientCLM_comp_localizedSpatialDifferenceQuotientH10CLM

     :
    (gradientCLM hΩ).comp
        (localizedSpatialDifferenceQuotientH10CLM
          hΩ η k h hηΩ hηshift) =
      localizedSpatialDifferenceQuotientSmoothGradientCLM hΩ η k h := (id
  (ContinuousLinearMap.ext fun x =>
    congrFun
      (DenseRange.equalizer (denseRange_smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ)
        (ContinuousLinearMap.continuous
          (gradientCLM hΩ ∘SL localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift))
        (ContinuousLinearMap.continuous (localizedSpatialDifferenceQuotientSmoothGradientCLM hΩ η k h))
        (funext fun φ =>
          id
            (id
              (Eq.mpr
                (id
                  (congrArg
                    (fun _a =>
                      (gradientCLM hΩ) _a =
                        (localizedSpatialDifferenceQuotientSmoothGradientCLM hΩ η k h)
                          ((smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ) φ))
                    (localizedSpatialDifferenceQuotientH10CLM_apply_smooth hΩ η k h φ hηΩ hηshift)))
                (gradientCLM_localizedSpatialDifferenceQuotientSmoothCoreLinearMap_apply hΩ η k h φ hηΩ hηshift)))))
      x))
end


end HypoellipticAleksandrov.Parabolic.Dirichlet
