module

public import DedekindZetaZeroFree.Adeles.Quotients.GreenIdentities.InteriorZeroExtension
public import DedekindZetaZeroFree.Metaplectic.Cubic.OrbifoldCharts.EquivariantScalarAndCotangentData
public import DedekindZetaZeroFree.Analysis.Sobolev.WeightedCovariant.CoordinateData

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree

attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

open KPContActualSectorSmoothTestModules KPContActualSectorTestEmbeddings
open KPContActualSectorTestDifferentialDescent KPContActualSectorChartEquivariantInputs
open KPContCotangentActualOverlap KPContCotangentOverlapRationalBranches KPContLocalNorm

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
variable {μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)} {hμG : μG.IsHaarMeasure}
variable {hR : R.adelicHaar = μG}
variable {realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H}

section FirstJetHelpers
open scoped ContDiff
open KPContActualCotangentChartRestriction
open KPContCotangentActualGenuineTwistIsotropy
theorem canonicalRealization :
    KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H :=
  actual_levelRealization_of_recipe F ζ hζ U R P H


open KPContActualSectorTestEmbeddings KPContActualCotangentMeasurableFamilies
open KPContActualCotangentChartRestriction KPContActualCotangentPieceHilbertSum

private theorem weighted_finite (a : ActualChart (U:=U) (H:=H))
    (L : Set (Space (3*d F))) (hL : IsCompact L)
    (hLω : L ⊆ (baseReindex (F:=F)).symm ⁻¹' omega a) :
    KPChartL2.weightedMeasure (3*d F) (chart a) (weight a) L < ⊤ := by
  have hsub : L ⊆ chart a := hLω
  rw [KPChartL2.weightedMeasure, withDensity_apply _ hL.measurableSet,
    Measure.restrict_restrict hL.measurableSet, Set.inter_eq_left.mpr hsub]
  have hi := ((scalarData (a := a)).locally_integrable_weight.mono_set hsub).integrableOn_isCompact hL
  apply lt_of_le_of_lt _ hi.hasFiniteIntegral
  apply lintegral_mono
  intro x
  change ENNReal.ofReal (weight a x) ≤ ‖weight a x‖ₑ
  rw [Real.enorm_eq_ofReal_abs]
  exact ENNReal.ofReal_le_ofReal (le_abs_self _)
private theorem compact_integrable (a : ActualChart (U:=U) (H:=H))
    (L : Set (Space (3*d F))) (hL : IsCompact L)
    (hLω : L ⊆ (baseReindex (F:=F)).symm ⁻¹' omega a)
    (g : Space (3*d F) → ℝ) (hg : Continuous g) :
    IntegrableOn g L (KPChartL2.weightedMeasure (3*d F) (chart a) (weight a)) := by
  haveI : IsFiniteMeasure ((KPChartL2.weightedMeasure (3*d F) (chart a) (weight a)).restrict L) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (weighted_finite a L hL hLω)⟩
  obtain ⟨C,hC⟩ := hL.exists_bound_of_continuousOn hg.continuousOn
  apply Integrable.of_bound (hg.aestronglyMeasurable) C
  exact ae_restrict_of_forall_mem hL.measurableSet hC

end FirstJetHelpers


end DedekindZetaZeroFree

end
