module

public import DedekindZetaZeroFree.Metaplectic.Cubic.GenuineSector.DifferentialAndCodifferential
public import DedekindZetaZeroFree.Metaplectic.Cubic.GenuineSector.TestL2Embeddings

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualSquareEndPartition

open KPContActualSectorSmoothTestModules KPContActualSectorTestDifferentialDescent

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

abbrev Cutoff := RealSmoothCutoff F ζ hζ U R P H

structure SectorMultiplier (η : Cutoff F ζ hζ U R P H) where
  op : KPContSectorClosedLpSubspace.H F ζ hζ R U →L[ℂ]
    KPContSectorClosedLpSubspace.H F ζ hζ R U
  ae_apply : ∀ u : KPContSectorClosedLpSubspace.H F ζ hζ R U,
    ((op u).val : KPContSectorCoveredQuotientVocabulary.CoveredSpherical F ζ hζ U → ℂ)
      =ᵐ[KPContSectorFixedPushforwardSupport.coveredMeasure F ζ hζ R U]
    fun x => (η.val (KPContSectorCoveredQuotientVocabulary.q F ζ hζ U x) : ℂ) *
      (u.val : KPContSectorCoveredQuotientVocabulary.CoveredSpherical F ζ hζ U → ℂ) x
  test_commutes : ∀ f : S_U F ζ hζ U R P H,
    op (KPContActualSectorTestEmbeddings.iota f) =
      KPContActualSectorTestEmbeddings.iota (scalarMultiply η f)

end DedekindZetaZeroFree.KPContActualSquareEndPartition

end
