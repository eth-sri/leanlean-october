module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CompactAveraging.Cuspidality
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Residual.NoncuspidalEigentests

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualAveragedEigentest
open KPContSectorCoveredQuotientVocabulary KPContSectorSmoothFramesSupport
open ResidualSphericalGeometry ResidualHilbertCenters
open _root_.DedekindZetaZeroFree.KPContSectorQuotientRelationsComparison renaming K_U_compact → K_U_compact
open _root_.DedekindZetaZeroFree renaming canonicalRealization → canonicalRealization
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 100000
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
local notation "V" => KPContActualAllCuspSource.level F ζ hζ C R P H U
local notation "Smooth" => KPContActualAllCuspSource.SmoothSections F ζ hζ C R P H U
local notation "Q" => KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
local instance averagedEigentestMeasurableSpace : MeasurableSpace (K_U F ζ hζ V) := borel (K_U F ζ hζ V)
local instance averagedEigentestBorelSpace : BorelSpace (K_U F ζ hζ V) := ⟨rfl⟩

theorem exists_averaged_eigentest (f : KPSmoothActualFlowData.X F ζ hζ → ℂ)
    (hf : KPLiteralRaw.Smooth F ζ hζ (f ∘ Q))
    (hc : ∀ ε g, f (Q (KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ ε*g)) =
      (chi F ζ hζ ε : ℂ)*f (Q g))
    (h2 : MemLp f 2 R.quotientHaar)
    (hz : ResidualCuspBoundary.UpperZero F ζ hζ (f ∘ Q)) (a : ℂ)
    (he : ∀g, KPMsGreenFlux.casimir F ζ hζ (f ∘ Q) g = a*f (Q g)) :
    ∃ ν : Measure (K_U F ζ hζ V), IsProbabilityMeasure ν ∧ ν.IsMulLeftInvariant ∧
      ∃ Z : Smooth, ∃ z : KPContActualAllCuspSource.Sector F ζ hζ C R P H U,
        KPContActualSmoothLineGluing.Represents F ζ hζ V R P H Z.val z ∧
        (∀g, originalScalar F ζ hζ V R P H Z (Q g) =
          ResidualRawAverage.average F ζ hζ (K_U F ζ hζ V) ν (f ∘ Q) g) ∧
        KPGlobalResidualConstruction.IncomingFiberOrthogonality.AllCuspMeanZero
          F ζ hζ C R P H U Z ∧
        (z,a • z) ∈ (sourceLaplacian F ζ hζ C R P H U).graph := by
  obtain ⟨ν, hν, hleft, Z, z, hrep, hp, hgraph⟩ :=
    exists_averaged_graph_eigentest F ζ hζ C R P H U f hf hc h2 a he
  let := hν
  let := hleft
  refine ⟨ν, hν, hleft, Z, z, hrep, hp, ?_, hgraph⟩
  apply ResidualCuspBoundary.allCuspMeanZero_of_original_upper_zero
  let A := H.atlas V
  let i : Fin A.componentCount := ⟨0,A.positive_componentCount⟩
  let j : KPMsGreenFlux.Cusps A := ⟨i,⟨0,(A.cuspAtlas i).positive_cuspCount⟩⟩
  have havg := ResidualAverageCusp.upperZero_average A j (K_U F ζ hζ V)
    (K_U_compact F ζ hζ V) ν (f ∘ Q) hf.1 (KPMsGreenFlux.IntrinsicAveraging.pullback_rational f) hz
  intro g
  change (∫ q : KPAdditiveQuotient F, (originalScalar F ζ hζ V R P H Z ∘ Q)
    (KPGlobalTorusFunctionData.N F ζ hζ (Quotient.out q)*g)
    ∂(KPWildKernelUpperBound.quotientHaar F)) = 0
  simpa only [Function.comp_apply, hp] using havg g
end DedekindZetaZeroFree.FourierContinuation.ResidualAveragedEigentest

end
