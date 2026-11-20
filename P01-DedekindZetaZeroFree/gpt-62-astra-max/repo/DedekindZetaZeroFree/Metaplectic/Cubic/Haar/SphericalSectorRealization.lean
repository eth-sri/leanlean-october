module

public import DedekindZetaZeroFree.Metaplectic.Cubic.Quotients.HaarLocalFiniteness
public import DedekindZetaZeroFree.Metaplectic.Cubic.GenuineL2.LineSectionIsometry

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualFixedSectorRealization

open KPContSectorCoveredQuotientVocabulary KPContSectorQuotientRelationsComparison
open KPContSectorFixedPushforwardSupport KPContSectorScalarLineAlgebra
open KPContSectorSmoothFramesSupport KPMsFixedHaarDisintegration

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

structure LevelRealization : Prop where
  covered_pushforward : coveredMeasure F ζ hζ R U =
    Measure.map (piTilde F ζ hζ U) R.quotientHaar

  support : LevelSupport F ζ hζ R P U

  sector_line_norm : ∀ u : KPContSectorClosedLpSubspace.H F ζ hζ R U,
    ∃ s : KPContSectorLineL2Isometry.BorelL2Sections F ζ hζ U R P H,
      KPContSectorLineL2Isometry.sectorLineIsometry F ζ hζ U R P H u =
        KPContSectorLineL2Isometry.mk F ζ hζ U R P H s ∧
      ‖u‖ ^ 2 = (KPContSectorLineL2Isometry.normIntegral F ζ hζ U R P H s.val).toReal

  norm_integrals : ∀ f : GenuineCoveredScalars F ζ hζ U, Measurable f.val →
    KPContSectorFixedLineNormIntegrals.NormIdentities F ζ hζ U R P H f

  chart_restriction : ∀ (f : GenuineCoveredScalars F ζ hζ U)
      (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
      (O : KPContSectorPhaseComponentCharts.OrbifoldChart F ζ hζ U R P H i x)
      (m : KPContSectorPhaseComponentCharts.PhaseSheets F ζ hζ U) (y : O.neighborhood),
    f.val (KPContSectorPhaseComponentCharts.coveredChart F ζ hζ U R P H i x O
      (Quotient.mk _ (m,y))).val =
        (phaseCoefficient F ζ hζ U R P H (S F ζ hζ U R P H f) i m y.val : ℂ)

end DedekindZetaZeroFree.KPContActualFixedSectorRealization

namespace DedekindZetaZeroFree

open KPContSectorCoveredQuotientVocabulary KPContSectorQuotientRelationsComparison
open KPContSectorFixedPushforwardSupport KPContSectorScalarLineAlgebra
open KPContSectorSmoothFramesSupport KPMsFixedHaarDisintegration

end DedekindZetaZeroFree

end
