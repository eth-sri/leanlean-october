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
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

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

theorem actual_levelRealization_of_recipe
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P) :
    KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H := by
  have hpos : R.quotientHaar.IsOpenPosMeasure :=
    (KPSmoothLocalQuotientCharts.quotient_full_support F ζ hζ R).1
  refine
    { covered_pushforward := rfl
      support := levelSupport F ζ hζ R P hpos U
      sector_line_norm := by
        intro u
        obtain ⟨g, hg, hgLp, hgu, f, hf, hfLp, hfavg, hfLp_toLp, heq, hzero⟩ :=
          KPContSectorExactBorelRepresentatives.exists_exact_borel_representative
            F ζ hζ R U u
        let f' : GenuineCoveredScalars F ζ hζ U := ⟨f, heq⟩
        let Fb : KPContSectorLineL2Isometry.BorelL2Scalars F ζ hζ U R :=
          ⟨f', ⟨hf, by simpa [f'] using hfLp⟩⟩
        have hFb : Fb.property.2.toLp Fb.val.val =
            (u : KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R U) := by
          simpa [Fb, f'] using hfLp_toLp
        refine ⟨KPContSectorLineL2Isometry.borelS F ζ hζ U R P H Fb, ?_, ?_⟩
        · exact KPContSectorLineL2Isometry.sectorLineIsometry_representative
            F ζ hζ U R P H u Fb hFb
        · rw [show ‖u‖ =
              ‖KPContSectorLineL2Isometry.sectorLineIsometry F ζ hζ U R P H u‖ from
              (LinearIsometryEquiv.norm_map _ u).symm,
            KPContSectorLineL2Isometry.sectorLineIsometry_representative
              F ζ hζ U R P H u Fb hFb]
          exact (kp_cont_sector_line_l2_isometry F ζ hζ U R P H).norm_formula
            (KPContSectorLineL2Isometry.borelS F ζ hζ U R P H Fb)
      norm_integrals := fun f hf =>
        kp_cont_sector_fixed_line_norm_integrals F ζ hζ U R P H f hf
      chart_restriction := fun f i x O m y =>
        orbifold_restriction_commutes F ζ hζ U R P H f i x O m y }

end DedekindZetaZeroFree

end
