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
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω)
    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo
      (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    ∃ C : ℝ, ∀ φ : PDE.WeakTestFunction Ω,
      ‖localizedSpatialDifferenceQuotientSmoothCoreLinearMap
          hΩ η k h hηΩ φ‖ ≤ C *
        ‖smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ‖ := by
  refine ⟨2 * (1 + d * (K + 1)) / |h|, ?_⟩
  intro φ
  exact norm_localizedSpatialDifferenceQuotientSmoothCoreLinearMap_apply_le
    hΩ η k h φ hηΩ hηshift

set_option linter.unusedVariables false in
/-- The localized spatial quotient extended from the actual smooth core to
the complete zero-boundary Sobolev graph. The forward collar fixes the
regime in which the advertised core agreement and norm bound hold. -/
@[nolint unusedArguments]
def localizedSpatialDifferenceQuotientH10CLM
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω)
    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo
      (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
  (localizedSpatialDifferenceQuotientSmoothCoreLinearMap
    hΩ η k h hηΩ).extendOfNorm
      (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ)

variable {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ} (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K) (k : Fin d)

/-- The extended quotient agrees with the literal bounded map on every
actual bundled smooth test. -/
theorem localizedSpatialDifferenceQuotientH10CLM_apply_smooth
     (h : ℝ) (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo
      (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    localizedSpatialDifferenceQuotientH10CLM
        hΩ η k h hηΩ hηshift
        (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ) =
      localizedSpatialDifferenceQuotientSmoothCoreLinearMap
        hΩ η k h hηΩ φ := LinearMap.extendOfNorm_eq
    (denseRange_smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ)
    (exists_localizedSpatialDifferenceQuotientSmoothCore_bound
      hΩ η k h hηΩ hηshift) φ

/-- The value component of the extended quotient is exactly the
quotient-level scalar operator. -/
theorem valueCLM_comp_localizedSpatialDifferenceQuotientH10CLM
     (h : ℝ)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo
      (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    (valueCLM hΩ).comp
        (localizedSpatialDifferenceQuotientH10CLM
          hΩ η k h hηΩ hηshift) =
      (localizedSpatialDifferenceQuotientL2
        hΩ.measurableSet η k h).comp (valueCLM hΩ) := by
  let e  :=
    smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ
  let q  :=
    (valueCLM hΩ).comp
      (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift)
  let r  :=
    (localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η k h).comp
      (valueCLM hΩ)
  apply ContinuousLinearMap.ext
  exact fun x => congrFun
    ((denseRange_smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ).equalizer
      q.continuous r.continuous (by
      funext φ
      change valueCLM hΩ
          (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift
            _) =
        localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η k h
          (valueCLM hΩ
            _)
      rw [localizedSpatialDifferenceQuotientH10CLM_apply_smooth]
      exact valueCLM_localizedSpatialDifferenceQuotientSmoothCoreLinearMap_apply
        hΩ η k h φ hηΩ hηshift)) x

/-- The gradient component of the extended quotient is exactly the
assembled quotient-level vector operator. -/
theorem gradientCLM_comp_localizedSpatialDifferenceQuotientH10CLM
     (h : ℝ)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : Set.MapsTo
      (fun y : PDE.Vec d => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω) :
    (gradientCLM hΩ).comp
        (localizedSpatialDifferenceQuotientH10CLM
          hΩ η k h hηΩ hηshift) =
      localizedSpatialDifferenceQuotientSmoothGradientCLM hΩ η k h := by
  let e  :=
    smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ
  let q  :=
    (gradientCLM hΩ).comp
      (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift)
  let r  :=
    localizedSpatialDifferenceQuotientSmoothGradientCLM hΩ η k h
  apply ContinuousLinearMap.ext
  exact fun x => congrFun
    ((denseRange_smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ).equalizer
      q.continuous r.continuous (by
      funext φ
      change gradientCLM hΩ
          (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift
            _) =
        localizedSpatialDifferenceQuotientSmoothGradientCLM hΩ η k h
          _
      rw [localizedSpatialDifferenceQuotientH10CLM_apply_smooth]
      exact gradientCLM_localizedSpatialDifferenceQuotientSmoothCoreLinearMap_apply
        hΩ η k h φ hηΩ hηshift)) x

end HypoellipticAleksandrov.Parabolic.Dirichlet
