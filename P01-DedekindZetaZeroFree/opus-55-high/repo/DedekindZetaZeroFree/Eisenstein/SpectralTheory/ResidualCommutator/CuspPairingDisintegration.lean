module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspidalOrthogonality.CentralAveraging

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped Classical NumberField ENNReal Topology
open MeasureTheory
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.SourceCuspidalOrthogonality.Transport
open KPMsFixedHaarDisintegration KPContSectorCoveredQuotientVocabulary KPContSectorFixedPushforwardSupport
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : SphericalTransport F ζ hζ) (H : AllLevels F ζ hζ R P) (U : Level F ζ hζ)
 theorem covered_integral_cusp_disintegration (Y : ℝ)
    (hY : AdmissibleCutoff (H.atlas U) Y)
    (g : CoveredSpherical F ζ hζ U → ℂ)
    (hg : Integrable g (coveredMeasure F ζ hζ R U))
    (hgm : Measurable g)
    (hsupp : ∀ v, q F ζ hζ U v ∉ cuspEnds (H.atlas U) Y → g v = 0)
    : ∃ a : Spherical F ζ hζ U → ℂ, Measurable a ∧
      (∀ v, a (q F ζ hζ U v) = centralComplexAverage F ζ hζ U g v) ∧
      (∫ v, g v ∂coveredMeasure F ζ hζ R U) =
        ((H.disintegration U).beta Set.univ).toReal *
          ∫ r : Set.Ioi Y, ∫ ω, ∫ x, a ((H.disintegration U).chart Y hY (x,r))
            ∂(H.disintegration U).unipotent ω ∂probability (H.atlas U) (H.disintegration U).beta
            ∂cuspRadial Y := by
  obtain ⟨a,ha,he⟩ := exists_complex_borel_descent F ζ hζ U g hgm
  refine ⟨a,ha,he,?_⟩
  rw [integral_complex_borel_descent F ζ hζ R U P g hg a ha he]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (complex_borel_descent_zero_off F ζ hζ U g a he _ hsupp)]
  exact integral_cusp_disintegration F ζ hζ R P H U Y hY a
    ((complex_borel_descent_integrable F ζ hζ R U P g hg a ha he).restrict)

end DedekindZetaZeroFree.KPGlobalResidualConstruction.SourceCuspidalOrthogonality.Transport
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.SourceCuspidalOrthogonality.Bridge
open KPContSectorCoveredQuotientVocabulary KPContSectorFixedPushforwardSupport
open KPContActualCutoffSmoothDescent
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
local notation "V" => level F ζ hζ C R P H U
local notation "A" => H.atlas V
local notation "D" => H.disintegration V
local notation "CS" => KPMsFixedHaarDisintegration.CrossSection A
local notation "X" => Covered F ζ hζ C R P H U

end DedekindZetaZeroFree.KPGlobalResidualConstruction.SourceCuspidalOrthogonality.Bridge

end
