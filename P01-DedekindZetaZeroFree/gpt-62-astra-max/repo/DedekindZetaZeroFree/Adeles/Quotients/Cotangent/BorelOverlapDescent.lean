module

public import DedekindZetaZeroFree.Adeles.Quotients.Cotangent.OverlapNullEquivalence
public import DedekindZetaZeroFree.Metaplectic.Cubic.OrbifoldCharts.IntegralDescent

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualCotangentBorelOverlapDescent

open KPContActualCotangentCountableShrinking
open KPContCotangentOverlapRationalBranches KPContCotangentOverlapNullEquivalence

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
    {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
    {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
    {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

end DedekindZetaZeroFree.KPContActualCotangentBorelOverlapDescent

namespace DedekindZetaZeroFree

open KPContActualCotangentCountableShrinking
open KPContCotangentFiniteQuotientBorel KPContCotangentChartDescentIntegrals

section LevelRealizationHelper

open KPContSectorCoveredQuotientVocabulary KPContSectorQuotientRelationsComparison
open KPContSectorFixedPushforwardSupport KPContSectorScalarLineAlgebra
open KPContSectorSmoothFramesSupport KPMsFixedHaarDisintegration

private theorem levelRealization_of_recipe
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P) :
    KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H := by
  have hpos : R.quotientHaar.IsOpenPosMeasure :=
    (KPSmoothLocalQuotientCharts.quotient_full_support F ζ hζ R)
  refine
    {
      covered_pushforward := rfl
      support := levelSupport F ζ hζ R P hpos U
      sector_line_norm := by
        intro u
        obtain ⟨g, hg, hgLp, f, hf, hfLp, hfLp_toLp, heq⟩ :=
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
        orbifold_restriction_commutes F ζ hζ U R P H f i x O m y
       }

theorem actual_levelRealization_of_recipe
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P) :
    KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H :=
  levelRealization_of_recipe F ζ hζ U R P H

end LevelRealizationHelper

theorem exists_nonsingular_chart_enumeration
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (hR : R.adelicHaar = μG)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (cover : CountableCover F ζ hζ U R P H)
    (a : ShrunkChart F ζ hζ U R P H) (n : ℕ) :
    Nonempty (KPContCotangentCorrectedNullEquivalence.NonsingularEnumeration2 a (cover.chart n)) := by
  obtain ⟨e⟩ := kp_cont_cotangent_overlap_rational_branches F ζ hζ μG hμG U R hR P H
    (levelRealization_of_recipe F ζ hζ U R P H) cover a (every_shrunkChart_properties F ζ hζ U R P H a) n
  exact ⟨KPContCotangentCorrectedNullEquivalence.withNonsingularity2 e⟩

end DedekindZetaZeroFree

end
