module

public import DedekindZetaZeroFree.Theta.Periods.Cusps.CrossTestIntegralTransport

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open scoped Classical NumberField Topology ENNReal NNReal BigOperators
open MeasureTheory
namespace DedekindZetaZeroFree.CurrentBoundaryShapeTransport
open KPMsActualAngularSource KPMsNativeOffsetMass KPMsNativeOffsetComparison
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
    {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
    (M : NativeMeasuredSource F ζ hζ R P) (V : Level F ζ hζ)

theorem weighted_cross_cancel (φ : G F ζ hζ → ℂ)
    (dk : Measure (KPMsGreenFlux.K F)) :
    (∫ ω, ∫ k, crossTest (R:=R) (P:=P) V φ (ω,k) ∂dk
      ∂weightedBeta F ζ hζ R P (nativeRecipe F ζ hζ R P) V) =
    ∫ ω, ∫ k, φ (KPMsGreenFlux.compactInsertion F ζ hζ k *
      (KPBoundedCuspFrames.actualFiniteRepresentative
        (nativeAtlas F ζ hζ R P (nativeRecipe F ζ hζ R P) V) ω.1).val) ∂dk
      ∂(nativeDisintegration F ζ hζ R P (nativeRecipe F ζ hζ R P) V).beta := by
  unfold weightedBeta
  let cuspOffset₀ := cuspOffset F ζ hζ R P (nativeRecipe F ζ hζ R P) V
  rw [integral_withDensity_eq_integral_toReal_smul (KPMsActualNativeWeightedShapeMeasure.cuspDensity_measurable
    (nativeAtlas F ζ hζ R P (nativeRecipe F ζ hζ R P) V)
    (fun j => ENNReal.ofReal (cuspOffset₀ j).val))
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [] with ω
  simp only [crossTest,integral_const_mul,
    ENNReal.toReal_ofReal (cuspOffset₀ ω.1).property.le,
    RCLike.real_smul_eq_coe_mul,← mul_assoc]
  change (((cuspOffset₀ ω.1).val:ℂ) *
    ((cuspOffset₀ ω.1).val:ℂ)⁻¹) * _ = _
  rw [mul_inv_cancel₀ (show ((cuspOffset₀ ω.1).val:ℂ) ≠ 0 by
    exact_mod_cast (cuspOffset₀ ω.1).property.ne'),one_mul]

theorem full_mass_cross_cancel (φ : G F ζ hζ → ℂ) (hφ : Continuous φ)
    (dk : Measure (KPMsGreenFlux.K F)) [IsFiniteMeasure dk] :
    ((fullMass M).toReal:ℂ) *
      (∫ ω, ∫ k, crossTest (R:=R) (P:=P) V φ
        (M.shape V (fullToLevel F ζ hζ (nativeDatum F ζ hζ) (cofinalLevel F ζ hζ V) ω),k)
        ∂dk ∂fullNu M) =
    ∫ ω, ∫ k, φ (KPMsGreenFlux.compactInsertion F ζ hζ k *
      (KPBoundedCuspFrames.actualFiniteRepresentative
        (nativeAtlas F ζ hζ R P (nativeRecipe F ζ hζ R P) V) ω.1).val) ∂dk
      ∂(nativeDisintegration F ζ hζ R P (nativeRecipe F ζ hζ R P) V).beta := by
  rw [cross_full_integral M V φ hφ dk,normalizedShapeBeta,integral_smul_measure]
  simp only [ENNReal.toReal_inv,RCLike.real_smul_eq_coe_mul,Complex.ofReal_inv,← mul_assoc]
  have hm : ((fullMass M).toReal:ℂ) * (((fullMass M).toReal)⁻¹:ℝ) = 1 := by
    exact_mod_cast mul_inv_cancel₀ (ENNReal.toReal_pos (fullMass_pos M).ne' (fullMass_ne_top M)).ne'
  change (((fullMass M).toReal:ℂ) * (((fullMass M).toReal)⁻¹:ℝ)) * _ = _
  rw [hm,one_mul]
  exact weighted_cross_cancel V φ dk
end DedekindZetaZeroFree.CurrentBoundaryShapeTransport

end
