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

set_option linter.unusedVariables false in
/-- The localized spatial quotient extended from the actual smooth core to
the complete zero-boundary Sobolev graph. The forward collar fixes the
regime in which the advertised core agreement and norm bound hold. -/
@[nolint unusedArguments]
noncomputable def localizedSpatialDifferenceQuotientH10CLM
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω)
    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : η.ShiftMapsInto k h Ω) :
    H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
  (localizedSpatialDifferenceQuotientSmoothCoreLinearMap
    hΩ η k h hηΩ).extendOfNorm
      (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ)

/-- The extended quotient agrees with the literal bounded map on every
actual bundled smooth test. -/
theorem localizedSpatialDifferenceQuotientH10CLM_apply_smooth
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω)
    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : η.ShiftMapsInto k h Ω) :
    localizedSpatialDifferenceQuotientH10CLM
        hΩ η k h hηΩ hηshift
        (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ) =
      localizedSpatialDifferenceQuotientSmoothCoreLinearMap
        hΩ η k h hηΩ φ := by
  exact LinearMap.extendOfNorm_eq
    (denseRange_smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ)
    (exists_smoothH10Core_bound hΩ
      ((localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η k h).comp (valueCLM hΩ))
      (localizedSpatialDifferenceQuotientSmoothGradientCLM hΩ η k h)
      (fun φ => valueCLM_localizedSpatialDifferenceQuotientSmoothCoreLinearMap_apply
        hΩ η k h φ hηΩ hηshift)
      (fun φ => gradientCLM_localizedSpatialDifferenceQuotientSmoothCoreLinearMap_apply
        hΩ η k h φ hηΩ hηshift)) φ

/-- Agreement on the smooth core determines any continuous linear map on `H¹₀`. -/
theorem smoothH10Core_ext {d : ℕ} {Ω : Set (PDE.Vec d)} {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {hΩ : IsOpen Ω}
    {Q R : H10HilbertGraph hΩ →L[ℝ] Y}
    (h : ∀ φ, Q (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ) =
      R (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ)) : Q = R :=
  ContinuousLinearMap.ext <| congrFun <|
    (denseRange_smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ).equalizer
      Q.continuous R.continuous (funext h)

section
variable {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ} (hΩ : IsOpen Ω)
  (η : PDE.QuantitativeSmoothCutoff inner outer K) (k : Fin d) (h : ℝ) (hηΩ : tsupport η.toFun ⊆ Ω)
  (hηshift : η.ShiftMapsInto k h Ω)

/-- The value component of the extended quotient is exactly the
quotient-level scalar operator. -/
theorem valueCLM_comp_localizedSpatialDifferenceQuotientH10CLM :
    (valueCLM hΩ).comp
        (localizedSpatialDifferenceQuotientH10CLM
          hΩ η k h hηΩ hηshift) =
      (localizedSpatialDifferenceQuotientL2
        hΩ.measurableSet η k h).comp (valueCLM hΩ) := by
  apply smoothH10Core_ext
  intro φ
  simp only [ContinuousLinearMap.comp_apply, localizedSpatialDifferenceQuotientH10CLM_apply_smooth]
  exact valueCLM_localizedSpatialDifferenceQuotientSmoothCoreLinearMap_apply hΩ η k h φ hηΩ hηshift

/-- The gradient component of the extended quotient is exactly the
assembled quotient-level vector operator. -/
theorem gradientCLM_comp_localizedSpatialDifferenceQuotientH10CLM :
    (gradientCLM hΩ).comp
        (localizedSpatialDifferenceQuotientH10CLM
          hΩ η k h hηΩ hηshift) =
      localizedSpatialDifferenceQuotientSmoothGradientCLM hΩ η k h := by
  apply smoothH10Core_ext
  intro φ
  simp only [ContinuousLinearMap.comp_apply, localizedSpatialDifferenceQuotientH10CLM_apply_smooth]
  exact gradientCLM_localizedSpatialDifferenceQuotientSmoothCoreLinearMap_apply hΩ η k h φ hηΩ hηshift

end

end HypoellipticAleksandrov.Parabolic.Dirichlet
