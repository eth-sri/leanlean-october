module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Residual.SectionMetricAndEigenfunctions

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualSphericalThreeL2
open KPContSectorSmoothFramesSupport KPContSectorLineL2Isometry
open ResidualSphericalGeometry
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

theorem original_l2_norm_finite (Z : smoothSections F ζ hζ U R P H)
    (h2 : MemLp (originalScalar F ζ hζ U R P H Z) 2 R.quotientHaar) :
    normIntegral F ζ hζ U R P H Z.val < ⊤ := by
  have hc : Continuous (scalarRepresentative F ζ hζ U R P H Z.val).val :=
    (continuous_iff F ζ hζ U R P H Z.val).mp (fun i => (Z.property i).continuous)
  apply (finite_integral_iff F ζ hζ U R P H Z.val
    (fun i => (Z.property i).continuous.measurable)).mpr
  apply (memLp_map_measure_iff hc.aestronglyMeasurable
    (KPContSectorQuotientRelationsComparison.piTilde_continuous F ζ hζ U).measurable.aemeasurable).mpr
  exact h2

end DedekindZetaZeroFree.FourierContinuation.ResidualSphericalThreeL2

end
