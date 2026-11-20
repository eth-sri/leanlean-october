module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.HaarLocalizers.AveragedZeroExtension
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.HaarLocalizers.NormalBallPullback
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.Localizers.OperatorReconstruction

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 100000
open scoped Classical NumberField ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree

open KPContActualFixedHaarCoreLocalizers KPContSectorSmoothFramesSupport KPContSectorLineL2Isometry
section
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

attribute [local instance 5000] KPContSectorLineL2Isometry.instNormedAddCommGroupL2Line
attribute [local instance 5000] KPContSectorLineL2Isometry.instNormedSpaceL2Line
attribute [local instance 5000] KPContSectorLineL2Isometry.instInnerProductSpaceL2Line

 abbrev instTopologicalSpaceL2LineLocal : TopologicalSpace (L2Line F ζ hζ U R P H) :=
  (KPContSectorLineL2Isometry.instNormedAddCommGroupL2Line F ζ hζ U R P H).toSeminormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

attribute [local instance 5000] instTopologicalSpaceL2LineLocal

 abbrev instAddCommMonoidL2LineLocal : AddCommMonoid (L2Line F ζ hζ U R P H) :=
  (KPContSectorLineL2Isometry.instNormedAddCommGroupL2Line F ζ hζ U R P H).toSeminormedAddCommGroup.toAddCommMonoid

attribute [local instance 5000] instAddCommMonoidL2LineLocal

 abbrev instTopologicalSpaceHULocal : TopologicalSpace (H_U F ζ hζ U R) :=
  (inferInstance : NormedAddCommGroup (H_U F ζ hζ U R)).toSeminormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

attribute [local instance 5000] instTopologicalSpaceHULocal

 abbrev instTopologicalSpaceHKLocal (K : Set (X_U F ζ hζ U)) :
    TopologicalSpace (H_K F ζ hζ U R P H K) :=
  (inferInstance : NormedAddCommGroup (H_K F ζ hζ U R P H K)).toSeminormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

attribute [local instance 5000] instTopologicalSpaceHKLocal

 abbrev instAddCommMonoidHKLocal (K : Set (X_U F ζ hζ U)) :
    AddCommMonoid (H_K F ζ hζ U R P H K) :=
  (inferInstance : NormedAddCommGroup (H_K F ζ hζ U R P H K)).toSeminormedAddCommGroup.toAddCommMonoid

attribute [local instance 5000] instAddCommMonoidHKLocal

end

theorem kp_cont_actual_fixed_haar_core_localizers
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ) (hR : R.adelicHaar = μG)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (K : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)) (hK : IsCompact K) :
    Nonempty (KPContActualFixedHaarCoreLocalizers.Localizers F ζ hζ U R P H K hK) := by
  obtain ⟨M,hM⟩ := KPCoreChartLocalizers.actual_realization_and_localizers F ζ hζ H.totallyComplex U (H.atlas U)
  obtain ⟨C⟩ := hM K hK
  choose D hD hDb using (fun i => KPCoreChartLocalizers.cutoff_derivative_bounds (C.smooth_cutoff i) (C.compact_cutoff i))
  have hcut : ∀ i x, |C.cutoff i x| ≤ D i 0 := by
    intro i x
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hDb i 0 x
  have hphi : ∀ i x, |C.phi i x| ≤ D i 0 := by
    intro i x
    by_cases hx : x ∈ (C.chart i).O F ζ hζ H.totallyComplex U
    · obtain ⟨y,hy,rfl⟩ := hx
      have hh := hcut i y
      rw [C.cutoff_formula,Set.indicator_of_mem hy] at hh
      exact hh
    · have hz : C.phi i x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (C.support_phi i h))
      rw [hz,abs_zero]
      exact hD i 0
  have hchart := fun i => KPFixedHaarLocalizersBodies.actual_chart_measure F ζ hζ U R P H (C.chart i)
  choose T hTn hT using (fun i => KPFixedHaarNormalBallMaps.chartPullback_exists F ζ hζ U R P H
    (C.chart i) (C.cutoff i) (C.smooth_cutoff i) (C.compact_cutoff i) (C.support_cutoff i)
    (C.invariant_cutoff i) (D i 0) (hD i 0) (hcut i) (hchart i))
  choose Rmap hRn hRf using (fun i => KPFixedHaarNormalBallMaps.averagedZeroExtension_exists F ζ hζ U R P H
    K hK (C.chart i) (hchart i))
  choose B hB using (fun i => KPFixedHaarLocalizersBodies.metric_upper_bound F ζ hζ U R P H (C.chart i))
  refine ⟨{
    count := C.count
    chart := C.chart
    chart_measure := hchart
    lower := fun i => ((H.disintegration U).componentWeight (C.chart i).component).toReal * (C.chart i).lower
    upper := fun i => ((H.disintegration U).componentWeight (C.chart i).component).toReal * (C.chart i).upper
    positive_lower := fun i => (KPFixedHaarLocalizersBodies.actualWeight_bounds F ζ hζ U R P H (C.chart i)).1
    density_bounds := fun i => (KPFixedHaarLocalizersBodies.actualWeight_bounds F ζ hζ U R P H (C.chart i)).2
    cutoff := C.cutoff
    smooth_cutoff := C.smooth_cutoff
    support_cutoff := C.support_cutoff
    derivativeBound := D
    nonnegative_derivativeBound := hD
    derivative_bounds := fun i k x hx => hDb i k x
    ellipticity := C.ellipticity
    metricUpper := B
    positive_ellipticity := C.positive_ellipticity
    metric_bounds := fun i x hx ξ => ⟨C.uniform_ellipticity i x (subset_closure (C.support_cutoff i hx)) ξ,
      hB i x (subset_closure (C.support_cutoff i hx)) ξ⟩
    T := T
    T_formula := hT
    Rmap := Rmap
    reconstruction := KPFixedHaarLocalizersBodies.finite_reconstruction F ζ hζ U R P H
      K hK C.chart C.phi C.smooth_phi C.support_phi
      (fun b hb => C.partition b (C.covers_compact hb)) C.cutoff C.cutoff_formula C.invariant_cutoff
      (fun i => D i 0) (fun i => hD i 0) hphi T hT Rmap hRf hchart
  }⟩

end DedekindZetaZeroFree

end
