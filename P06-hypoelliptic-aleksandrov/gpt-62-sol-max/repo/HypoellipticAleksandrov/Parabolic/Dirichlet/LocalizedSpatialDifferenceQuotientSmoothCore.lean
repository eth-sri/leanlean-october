module

public import HypoellipticAleksandrov.Measure.HilbertVectorLpAssembly
public import HypoellipticAleksandrov.Parabolic.Dirichlet.GalerkinDense
public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientSmoothGraph
public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialSobolevNorm

/-!
# Bounded localized quotients on the actual smooth `H¹₀` core

This module constructs the cutoff-localized forward spatial difference
quotient only on bundled smooth compactly supported tests and records its
quotient-level value and gradient.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped ENNReal

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The localized difference quotient as a linear map on bundled smooth tests. -/
noncomputable def localizedSpatialDifferenceQuotientWeakTestLinearMap
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (hηΩ : tsupport η.toFun ⊆ Ω) :
    PDE.WeakTestFunction Ω →ₗ[ℝ] PDE.WeakTestFunction Ω where
  toFun φ := localizedSpatialDifferenceQuotientWeakTest η k h φ hηΩ
  map_add' φ ψ := by
    apply PDE.WeakTestFunction.ext
    funext y
    simp only [localizedSpatialDifferenceQuotientWeakTest_apply,
      PDE.WeakTestFunction.add_toFun, Pi.add_apply]
    ring
  map_smul' c φ := by
    apply PDE.WeakTestFunction.ext
    funext y
    simp only [localizedSpatialDifferenceQuotientWeakTest_apply,
      PDE.WeakTestFunction.smul_toFun, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem norm_h10HilbertGraph_le_value_add_gradient
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (u : H10HilbertGraph hΩ) :
    ‖u‖ ≤ ‖valueCLM hΩ u‖ + ‖gradientCLM hΩ u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  nlinarith only [norm_sq_h10HilbertGraph hΩ u,
    mul_nonneg (norm_nonneg (valueCLM hΩ u)) (norm_nonneg (gradientCLM hΩ u))]

section
variable {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ} (hΩ : IsOpen Ω)
  (η : PDE.QuantitativeSmoothCutoff inner outer K) (k : Fin d) (h : ℝ)
include inner outer K η k h

/-- The cutoff-localized forward spatial quotient as a linear map from
actual bundled smooth tests into the zero-boundary Sobolev graph. -/
noncomputable def localizedSpatialDifferenceQuotientSmoothCoreLinearMap (hηΩ : tsupport η.toFun ⊆ Ω) :
    PDE.WeakTestFunction Ω →ₗ[ℝ] H10HilbertGraph hΩ :=
  (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ).comp
    (localizedSpatialDifferenceQuotientWeakTestLinearMap η k h hηΩ)

/-- The quotient-safe vector `L²` expression for the gradient of the
localized quotient on the actual smooth core. -/
noncomputable def localizedSpatialDifferenceQuotientSmoothGradientCLM :
    H10HilbertGraph hΩ →L[ℝ]
      PDE.HilbertVectorLp Ω (2 : ℝ≥0∞) :=
  PDE.hilbertVectorLpAssemble fun j =>
    (cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η j k h).comp
        (valueCLM hΩ) +
      (localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η k h).comp
        ((PDE.hilbertVectorLpCoord Ω (2 : ℝ≥0∞) j).comp
          (gradientCLM hΩ))

end

section
variable {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ} (hΩ : IsOpen Ω)
  (η : PDE.QuantitativeSmoothCutoff inner outer K) (k : Fin d) (h : ℝ) (φ : PDE.WeakTestFunction Ω)
  (hηΩ : tsupport η.toFun ⊆ Ω) (hηshift : η.ShiftMapsInto k h Ω)
include hηshift

/-- The smooth-core value class is the quotient-level localized value
operator applied to the exact dense-core inclusion. -/
theorem valueCLM_localizedSpatialDifferenceQuotientSmoothCoreLinearMap_apply :
    valueCLM hΩ
      (localizedSpatialDifferenceQuotientSmoothCoreLinearMap
        hΩ η k h hηΩ φ) =
      localizedSpatialDifferenceQuotientL2 hΩ.measurableSet η k h
        (valueCLM hΩ
          (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ)) := by
  apply MeasureTheory.Lp.ext
  exact (ae_valueCLM_smoothCompactlySupportedH1HilbertGraph hΩ
    (localizedSpatialDifferenceQuotientWeakTest η k h φ hηΩ)).trans
    (localizedSpatialDifferenceQuotientL2_apply_ae_of_ae_eq hΩ.measurableSet η k h _ φ
      (ae_valueCLM_smoothCompactlySupportedH1HilbertGraph hΩ φ) hηshift).symm

/-- The smooth-core gradient class is the assembled quotient-safe vector
operator applied to the exact dense-core inclusion. -/
theorem gradientCLM_localizedSpatialDifferenceQuotientSmoothCoreLinearMap_apply :
    gradientCLM hΩ
      (localizedSpatialDifferenceQuotientSmoothCoreLinearMap
        hΩ η k h hηΩ φ) =
      localizedSpatialDifferenceQuotientSmoothGradientCLM hΩ η k h
        (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ) := by
  apply PDE.hilbertVectorLp_ext
  intro j
  rw [localizedSpatialDifferenceQuotientSmoothGradientCLM,
    PDE.hilbertVectorLpCoord_hilbertVectorLpAssemble]
  exact localizedSpatialDifferenceQuotientWeakTest_gradientCoord_eq hΩ η k h φ hηΩ hηshift j

end

/-- Graph operators on the smooth core are bounded by their continuous receivers. -/
theorem exists_smoothH10Core_bound {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    {Q E : PDE.WeakTestFunction Ω →ₗ[ℝ] H10HilbertGraph hΩ}
    (V : H10HilbertGraph hΩ →L[ℝ] PDE.ScalarLp Ω 2)
    (G : H10HilbertGraph hΩ →L[ℝ] PDE.HilbertVectorLp Ω 2)
    (hv : ∀ φ, valueCLM hΩ (Q φ) = V (E φ))
    (hg : ∀ φ, gradientCLM hΩ (Q φ) = G (E φ)) :
    ∃ C : ℝ, ∀ φ, ‖Q φ‖ ≤ C * ‖E φ‖ := by
  refine ⟨‖V‖ + ‖G‖, fun φ => (norm_h10HilbertGraph_le_value_add_gradient hΩ _).trans ?_⟩
  rw [hv, hg, add_mul]
  exact add_le_add (V.le_opNorm _) (G.le_opNorm _)

end HypoellipticAleksandrov.Parabolic.Dirichlet
