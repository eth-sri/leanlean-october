module

public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.LocalCharts.FiniteIsotropyQuotientMeasure
public import DedekindZetaZeroFree.Metaplectic.Cubic.Haar.SphericalSectorRealization
public import DedekindZetaZeroFree.Geometry.Hyperbolic.Archimedean.RealCoordinatesAndVolume
public import DedekindZetaZeroFree.Analysis.Sobolev.LocalEmbeddingAndSmoothRepresentatives

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal
attribute [-instance] DedekindZetaZeroFree.CoreChartLocalizers.instMeasurableSpaceX
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualChartRestrictionDensity

open KPContSectorCoveredQuotientVocabulary KPContSectorPhaseComponentCharts
open KPContSectorSmoothFramesSupport KPContSectorLineL2Isometry KPContSectorScalarLineAlgebra
open KPContLocalNorm

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

def coordinates : Space (KPCuspLogShape.dimension F * 3) ≃ₜ SymmetricSpace F :=
  KPArchRealCoordinates.coordinates (KPCuspLogShape.dimension F)

def density (p : Space (KPCuspLogShape.dimension F * 3)) : ℝ :=
  KPArchRealCoordinates.density (KPCuspLogShape.dimension F) p

theorem coordinate_volume : Measure.map (coordinates F) volume =
    (volume : Measure (SymmetricSpace F)) := KPArchRealCoordinates.coordinate_volume (KPCuspLogShape.dimension F)

theorem density_smooth : ContDiff ℝ (⊤ : ℕ∞) (density F) := KPArchRealCoordinates.density_smooth (KPCuspLogShape.dimension F)

theorem density_positive (p : Space (KPCuspLogShape.dimension F * 3)) :
    0 < density F p := KPArchRealCoordinates.density_positive (KPCuspLogShape.dimension F) p

theorem density_bounds (A : LocalBall (KPCuspLogShape.dimension F * 3)) :
    ∃ a b : ℝ, 0 < a ∧ ∀ p ∈ KPContLocalCubeEmbedding.closedCarrier A,
      a ≤ density F p ∧ density F p ≤ b := by
  have hK :=
    isCompact_closedBall A.center A.radius
  have hne : (KPContLocalCubeEmbedding.closedCarrier A).Nonempty :=
    ⟨A.center, Metric.mem_closedBall_self A.radius_pos.le⟩
  obtain ⟨p, hp, hmin⟩ := hK.exists_isMinOn hne (density_smooth F).continuous.continuousOn
  obtain ⟨q, hq, hmax⟩ := hK.exists_isMaxOn hne (density_smooth F).continuous.continuousOn
  exact ⟨density F p, density F q, density_positive F p, fun z hz => ⟨hmin hz, hmax hz⟩⟩

theorem metric_volume : Measure.map (coordinates F)
    (volume.withDensity (fun p => ENNReal.ofReal (density F p))) =
      KPArch.hyperbolicVolume (KPCuspLogShape.dimension F) := KPArchRealCoordinates.metric_volume (KPCuspLogShape.dimension F)

section

variable (i : Fin (H.atlas U).componentCount)

def chartDomain (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x) : Set (Space (KPCuspLogShape.dimension F * 3)) :=
  coordinates F ⁻¹' O.neighborhood

def basePoint
    (p : Space (KPCuspLogShape.dimension F * 3)) : KPFiniteCuspAtlas.rawXU F ζ hζ U :=
  (H.atlas U).components ⟨i, Quotient.mk _ (coordinates F p)⟩

def isotropyOrder (x : SymmetricSpace F) : ℕ :=
  Nat.card (MulAction.stabilizer (Component F ζ hζ U R P H i) x)

end

section

variable (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x)

def chartMeasure : Measure (Space (KPCuspLogShape.dimension F * 3)) :=
  ((H.disintegration U).componentWeight i /
    (isotropyOrder F ζ hζ U R P H i x : ℝ≥0∞)) •
      ((volume.restrict (chartDomain F ζ hζ U R P H i x O)).withDensity
        (fun p => ENNReal.ofReal (density F p)))

include O in
theorem isotropyOrder_pos :
    0 < isotropyOrder F ζ hζ U R P H i x := by
  letI := chart_stabilizer_finite F ζ hζ U R P H i x O
  exact Nat.card_pos

theorem null_sets
    (A : LocalBall (KPCuspLogShape.dimension F * 3))
    (hA : KPContLocalCubeEmbedding.closedCarrier A ⊆ chartDomain F ζ hζ U R P H i x O) :
    (chartMeasure F ζ hζ U R P H i x O).restrict A.carrier ≪ volume.restrict A.carrier ∧
    volume.restrict A.carrier ≪ (chartMeasure F ζ hζ U R P H i x O).restrict A.carrier := by
  have hAD : A.carrier ⊆ chartDomain F ζ hζ U R P H i x O :=
    (Metric.ball_subset_closedBall).trans hA
  have hAmeas : MeasurableSet A.carrier := Metric.isOpen_ball.measurableSet
  have heq : (chartMeasure F ζ hζ U R P H i x O).restrict A.carrier =
      ((H.disintegration U).componentWeight i /
        (isotropyOrder F ζ hζ U R P H i x : ℝ≥0∞)) •
        ((volume.restrict A.carrier).withDensity (fun p => ENNReal.ofReal (density F p))) := by
    rw [chartMeasure, Measure.restrict_smul, restrict_withDensity hAmeas,
      Measure.restrict_restrict_of_subset hAD]
  have hc : ((H.disintegration U).componentWeight i /
      (isotropyOrder F ζ hζ U R P H i x : ℝ≥0∞)) ≠ 0 := by
    apply ENNReal.div_ne_zero.mpr
    constructor
    · exact ne_of_gt ((H.disintegration U).positive_componentWeight i)
    · exact ENNReal.natCast_ne_top _
  rw [heq]
  exact ⟨Measure.smul_absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _),
    (withDensity_absolutelyContinuous' ((ENNReal.measurable_ofReal.comp (density_smooth F).continuous.measurable).aemeasurable) (Filter.Eventually.of_forall fun p => ne_of_gt (ENNReal.ofReal_pos.mpr (density_positive F p)))).trans (Measure.absolutelyContinuous_smul hc)⟩

end

section

variable (f : GenuineCoveredScalars F ζ hζ U) (i : Fin (H.atlas U).componentCount)

def frameCoefficient (m : PhaseSheets F ζ hζ U)
    (p : Space (KPCuspLogShape.dimension F * 3)) : ℂ :=
  (liftFrame F ζ hζ U (coordinates F p)
    (phaseCoefficient F ζ hζ U R P H (S F ζ hζ U R P H f) i m
      (coordinates F p)) : ℂ)

theorem covered_coefficient (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x) (m : PhaseSheets F ζ hζ U)
    (p : Space (KPCuspLogShape.dimension F * 3))
    (hp : p ∈ chartDomain F ζ hζ U R P H i x O) :
    frameCoefficient F ζ hζ U R P H f i m p =
      f.val (coveredChart F ζ hζ U R P H i x O
        (Quotient.mk _ (m, (⟨coordinates F p, hp⟩ : O.neighborhood)))).val := (orbifold_restriction_commutes F ζ hζ U R P H f i x O m
      ⟨coordinates F p, hp⟩).symm

theorem frameCoefficient_class (ε : rootsOfUnity 3 F)
    (p : Space (KPCuspLogShape.dimension F * 3)) :
    frameCoefficient F ζ hζ U R P H f i (phaseClass F ζ hζ U ε) p =
      (chi F ζ hζ ε : ℂ) * (S F ζ hζ U R P H f i).val (coordinates F p) := phaseCoefficient_class F ζ hζ U R P H (S F ζ hζ U R P H f) i ε (coordinates F p)

end

section

variable (i : Fin (H.atlas U).componentCount) (γ : Component F ζ hζ U R P H i)

def overlapCoordinate
    (p : Space (KPCuspLogShape.dimension F * 3)) : Space (KPCuspLogShape.dimension F * 3) :=
  (coordinates F).symm ((γ : KPCuspArithmetic.PGL2 F) • coordinates F p)

def overlapTransition (ε : rootsOfUnity 3 F) : Circle :=
  chi F ζ hζ ε * chi F ζ hζ (((H.atlas U).line i).rho γ)⁻¹

theorem transition_unitary (ε : rootsOfUnity 3 F) :
    ‖(overlapTransition F ζ hζ U R P H i γ ε : ℂ)‖ = 1 :=
  Circle.norm_coe _

end

theorem frameCoefficient_overlap (f : GenuineCoveredScalars F ζ hζ U)
    (i : Fin (H.atlas U).componentCount) (m m' : PhaseSheets F ζ hζ U)
    (ε : rootsOfUnity 3 F) (γ : Component F ζ hζ U R P H i)
    (hm : m = phaseClass F ζ hζ U ε * m')
    (p : Space (KPCuspLogShape.dimension F * 3)) :
    frameCoefficient F ζ hζ U R P H f i m p =
      (overlapTransition F ζ hζ U R P H i γ ε : ℂ) *
        frameCoefficient F ζ hζ U R P H f i m'
          (overlapCoordinate F ζ hζ U R P H i γ p) := by
  obtain ⟨η, rfl⟩ := QuotientGroup.mk'_surjective (centralLevel F ζ hζ U) m'
  change m = phaseClass F ζ hζ U ε * phaseClass F ζ hζ U η at hm
  change frameCoefficient F ζ hζ U R P H f i m p =
    (overlapTransition F ζ hζ U R P H i γ ε : ℂ) *
      frameCoefficient F ζ hζ U R P H f i (phaseClass F ζ hζ U η)
        (overlapCoordinate F ζ hζ U R P H i γ p)
  rw [hm, ← map_mul, frameCoefficient_class, frameCoefficient_class]
  have hs := (S F ζ hζ U R P H f i).property.2 γ (coordinates F p)
  change (S F ζ hζ U R P H f i).val ((γ : KPCuspArithmetic.PGL2 F) • coordinates F p) =
    (chi F ζ hζ (((H.atlas U).line i).rho γ) : ℂ) *
      (S F ζ hζ U R P H f i).val (coordinates F p) at hs
  simp only [overlapCoordinate, Homeomorph.apply_symm_apply]
  rw [hs]
  simp only [overlapTransition, map_mul, map_inv, Circle.coe_mul, Circle.coe_inv]
  field_simp

theorem overlapCoordinate_quasiMeasurePreserving (i : Fin (H.atlas U).componentCount)
    (γ : Component F ζ hζ U R P H i) :
    Measure.QuasiMeasurePreserving (overlapCoordinate F ζ hζ U R P H i γ) volume volume := by
  let ν :=
    volume.withDensity (fun p => ENNReal.ofReal (density F p))
  let μ := KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)
  have hc : MeasurePreserving (coordinates F) ν μ :=
    ⟨(coordinates F).continuous.measurable, metric_volume F⟩
  have hvν : volume ≪ ν :=
    withDensity_absolutelyContinuous'
      ((ENNReal.measurable_ofReal.comp (density_smooth F).continuous.measurable).aemeasurable)
      (Filter.Eventually.of_forall fun p => ne_of_gt
        (ENNReal.ofReal_pos.mpr (density_positive F p)))
  exact ((((hc.symm (coordinates F).toMeasurableEquiv).quasiMeasurePreserving.comp (KPFiniteAdelicCuspEnds.arch_smul_measurePreserving F
    γ).quasiMeasurePreserving).comp hc.quasiMeasurePreserving).mono_left hvν).mono_right (withDensity_absolutelyContinuous _ _)

open scoped Pointwise in

theorem quotient_measure (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x) :
    Measure.map (basePoint F ζ hζ U R P H i) (chartMeasure F ζ hζ U R P H i x O) =
      (KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U).restrict
        (baseChartImage F ζ hζ U R P H i x O) := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := F)
  letI : Countable (Matrix (Fin 2) (Fin 2) F) := by
    change Countable (Fin 2 → Fin 2 → F); infer_instance
  letI : Countable (Matrix.GeneralLinearGroup (Fin 2) F) :=
    Function.Injective.countable Units.val_injective
  letI : Countable (KPCuspArithmetic.PGL2 F) :=
    Function.Surjective.countable Matrix.ProjGenLinGroup.mk_surjective
  let Γ := Component F ζ hζ U R P H i
  let μ := KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)
  let π := KPCuspSiegel.projection F Γ
  let j := KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative i)
  let T := MulAction.stabilizer Γ x
  letI : Finite T := chart_stabilizer_finite F ζ hζ U R P H i x O
  letI : Fintype T := Fintype.ofFinite T
  letI : MeasurableConstSMul Γ (SymmetricSpace F) :=
    ⟨fun g => (KPFiniteAdelicCuspEnds.arch_smul_measurePreserving F g.val).measurable⟩
  letI : SMulInvariantMeasure Γ (SymmetricSpace F) μ := by
    constructor; intro g s hs
    have hp := KPFiniteAdelicCuspEnds.arch_smul_measurePreserving F g.val
    change (KPArch.hyperbolicVolume _) ((fun z => g.val • z) ⁻¹' s) = _
    rw [← Measure.map_apply hp.measurable hs, hp.map_eq]
  have hΓ (g : Γ) : complexProjectiveEmbedding F g.val ∈ ArchComponent F ζ hζ U R P H i :=
    Subgroup.mem_map.mpr ⟨g.val, g.property, rfl⟩
  have hinv (g : T) : (g.val : Γ) • O.neighborhood = O.neighborhood := by
    let a : ArchComponent F ζ hζ U R P H i := ⟨complexProjectiveEmbedding F g.val.val, hΓ g.val⟩
    have ha : a ∈ MulAction.stabilizer (ArchComponent F ζ hζ U R P H i) x := by
      change complexProjectiveEmbedding F g.val.val • x = x
      rw [complexProjectiveEmbedding_smul]
      exact g.property
    have ho := O.invariant ⟨a,ha⟩
    change (fun z => complexProjectiveEmbedding F g.val.val • z) '' O.neighborhood = O.neighborhood at ho
    simp only [complexProjectiveEmbedding_smul] at ho
    exact ho
  have hsep (g : Γ) (z : SymmetricSpace F) (hz : z ∈ O.neighborhood)
      (hgz : g • z ∈ O.neighborhood) : g ∈ T := by
    let a : ArchComponent F ζ hζ U R P H i := ⟨complexProjectiveEmbedding F g.val, hΓ g⟩
    have ha : a ∈ MulAction.stabilizer (ArchComponent F ζ hζ U R P H i) x := by
      apply O.separated a
      refine ⟨g • z, ⟨z,hz,?_⟩,hgz⟩
      exact complexProjectiveEmbedding_smul F g.val z
    change complexProjectiveEmbedding F g.val • x = x at ha
    rwa [complexProjectiveEmbedding_smul] at ha
  have hlocal := CoreChartLocalizers.CutoffConstruction.finite_isotropy_quotient_measure
    μ T ((H.atlas U).cuspAtlas i).fundamentalDomain O.neighborhood
    ((H.atlas U).cuspAtlas i).measurable_fundamentalDomain O.isOpen.measurableSet
    ((H.atlas U).cuspAtlas i).isFundamentalDomain hinv hsep
  have hj : Topology.IsOpenEmbedding j := by
    have he : j = (H.atlas U).components ∘ Sigma.mk i := by
      funext z; exact ((H.atlas U).components_formula i z).symm
    rw [he]
    exact (H.atlas U).components.isOpenEmbedding.comp IsOpenEmbedding.sigmaMk
  letI : OpensMeasurableSpace (KPCuspSiegel.OrbitQuotient F Γ) := ⟨MeasurableSpace.generateFrom_le (fun s hs =>
      measurableSet_quotient.mpr ((hs.preimage (show Continuous π from continuous_quotient_mk')).measurableSet))⟩
  letI : BorelSpace (KPFiniteCuspAtlas.rawXU F ζ hζ U) := ⟨rfl⟩
  have hjm : Measurable j := hj.continuous.measurable
  have hπm : Measurable π := measurable_quotient_mk''
  have hb : basePoint F ζ hζ U R P H i = j ∘ π ∘ coordinates F := by
    funext p
    exact (H.atlas U).components_formula i _
  have hcoord : Measure.map (coordinates F)
      ((volume.restrict (chartDomain F ζ hζ U R P H i x O)).withDensity
        (fun p => ENNReal.ofReal (density F p))) = μ.restrict O.neighborhood := by
    unfold chartDomain
    rw [← restrict_withDensity ((coordinates F).continuous.measurable O.isOpen.measurableSet)]
    rw [← Measure.restrict_map (coordinates F).continuous.measurable O.isOpen.measurableSet,
      metric_volume]
  rw [chartMeasure, hb, Measure.map_smul _ (hjm.comp (hπm.comp (coordinates F).continuous.measurable)).aemeasurable,
    ← Function.comp_assoc, ← Measure.map_map (hjm.comp hπm) (coordinates F).continuous.measurable,
    hcoord, ← Measure.map_map hjm hπm]
  have hc : ((H.disintegration U).componentWeight i /
      (isotropyOrder F ζ hζ U R P H i x : ℝ≥0∞)) =
      (H.disintegration U).componentWeight i * (Fintype.card T : ℝ≥0∞)⁻¹ := by
    rw [div_eq_mul_inv]
    congr 2
    exact_mod_cast (Nat.card_eq_fintype_card)
  rw [hc, ← smul_smul, ← Measure.map_smul _ hjm.aemeasurable,
    ← Measure.map_smul _ hπm.aemeasurable]
  change Measure.map π ((Fintype.card T : ℝ≥0∞)⁻¹ • μ.restrict O.neighborhood) =
    (KPFiniteCuspAtlas.quotientVolume F Γ ((H.atlas U).cuspAtlas i).fundamentalDomain).restrict
      (π '' O.neighborhood) at hlocal
  rw [hlocal]
  have hB : baseChartImage F ζ hζ U R P H i x O = j '' (π '' O.neighborhood) := by
    unfold baseChartImage
    congr 1
    funext z
    exact (H.atlas U).components_formula i z
  have hpre : j ⁻¹' baseChartImage F ζ hζ U R P H i x O = π '' O.neighborhood := by
    rw [hB, Set.preimage_image_eq _ hj.injective]
  rw [← Measure.map_smul _ hjm.aemeasurable, ← Measure.restrict_smul]
  rw [← hpre, ← Measure.restrict_map hjm (baseChartImage_isOpen F ζ hζ U R P H i x O).measurableSet,
    Measure.map_smul _ hjm.aemeasurable]
  have hsub : baseChartImage F ζ hζ U R P H i x O ⊆ Set.range j := by
    rw [hB]; exact Set.image_subset_range _ _
  rw [← (H.disintegration U).component_measure i,
    Measure.restrict_restrict_of_subset hsub]

structure DensityIdentities : Prop where
  coordinate_volume : Measure.map (coordinates F) volume =
    (volume : Measure (SymmetricSpace F))
  density_smooth : ContDiff ℝ (⊤ : ℕ∞) (density F)
  density_positive : ∀ p, 0 < density F p
  metric_volume : Measure.map (coordinates F)
    (volume.withDensity (fun p => ENNReal.ofReal (density F p))) =
      KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)
  isotropy_positive : ∀ (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (_O : OrbifoldChart F ζ hζ U R P H i x),
    0 < isotropyOrder F ζ hζ U R P H i x

  quotient_measure : ∀ (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x),
    Measure.map (basePoint F ζ hζ U R P H i) (chartMeasure F ζ hζ U R P H i x O) =
      (KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U).restrict
        (baseChartImage F ζ hζ U R P H i x O)
  local_integral : ∀ (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x)
    (g : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ≥0∞), Measurable g →
    (∫⁻ b in baseChartImage F ζ hζ U R P H i x O, g b
      ∂KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U) =
    ((H.disintegration U).componentWeight i /
      (isotropyOrder F ζ hζ U R P H i x : ℝ≥0∞)) *
    ∫⁻ p in chartDomain F ζ hζ U R P H i x O,
      g (basePoint F ζ hζ U R P H i p) * ENNReal.ofReal (density F p)
  density_bounds : ∀ (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x)
    (A : LocalBall (KPCuspLogShape.dimension F * 3)),
    KPContLocalCubeEmbedding.closedCarrier A ⊆ chartDomain F ζ hζ U R P H i x O →
    ∃ a b : ℝ, 0 < a ∧ ∀ p ∈ KPContLocalCubeEmbedding.closedCarrier A,
      a ≤ density F p ∧ density F p ≤ b

  null_sets : ∀ (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x)
    (A : LocalBall (KPCuspLogShape.dimension F * 3)),
    KPContLocalCubeEmbedding.closedCarrier A ⊆ chartDomain F ζ hζ U R P H i x O →
    (chartMeasure F ζ hζ U R P H i x O).restrict A.carrier ≪ volume.restrict A.carrier ∧
    volume.restrict A.carrier ≪ (chartMeasure F ζ hζ U R P H i x O).restrict A.carrier

theorem densityIdentities : DensityIdentities F ζ hζ U R P H := by
  refine ⟨coordinate_volume F, density_smooth F, density_positive F, metric_volume F,
    isotropyOrder_pos F ζ hζ U R P H, quotient_measure F ζ hζ U R P H, ?_,
    fun _ _ _ A _ => density_bounds F A, null_sets F ζ hζ U R P H⟩
  intro i x O g hg
  have hb : Measurable (basePoint F ζ hζ U R P H i) := by
    have he : basePoint F ζ hζ U R P H i =
      fun p => Quotient.mk _ (coordinates F p, (H.atlas U).representative i) := by
      funext p
      exact (H.atlas U).components_formula i _
    rw [he]
    exact (continuous_quotient_mk'.comp
      ((coordinates F).continuous.prodMk continuous_const)).measurable
  rw [← quotient_measure F ζ hζ U R P H i x O, lintegral_map hg hb,
    chartMeasure, lintegral_smul_measure]
  congr 1
  rw [lintegral_withDensity_eq_lintegral_mul]
  · simp only [Pi.mul_apply, mul_comm]
  · exact (ENNReal.measurable_ofReal.comp (density_smooth F).continuous.measurable)
  · exact hg.comp hb

theorem basePoint_measurable (i : Fin (H.atlas U).componentCount) :
    Measurable (basePoint F ζ hζ U R P H i) := by
  have he : basePoint F ζ hζ U R P H i =
      fun p => Quotient.mk _ (coordinates F p, (H.atlas U).representative i) := by
    funext p; exact (H.atlas U).components_formula i _
  rw [he]
  exact (continuous_quotient_mk'.comp
    ((coordinates F).continuous.prodMk continuous_const)).measurable

section

variable (f : BorelL2Scalars F ζ hζ U R) (i : Fin (H.atlas U).componentCount)

theorem frameCoefficient_measurable (m : PhaseSheets F ζ hζ U) :
    Measurable (frameCoefficient F ζ hζ U R P H f.val i m) := by
  obtain ⟨ε, rfl⟩ := QuotientGroup.mk'_surjective (centralLevel F ζ hζ U) m
  change Measurable (frameCoefficient F ζ hζ U R P H f.val i (phaseClass F ζ hζ U ε))
  have he : frameCoefficient F ζ hζ U R P H f.val i (phaseClass F ζ hζ U ε) =
    fun p => (chi F ζ hζ ε : ℂ) *
      f.val.val (Quotient.mk (coveredRelation F ζ hζ U) (coordinates F p, (H.atlas U).representative i)) := by
    funext p; rw [frameCoefficient_class, S_apply]
  rw [he]
  apply Measurable.const_mul
  apply f.property.1.comp
  exact (continuous_quotient_mk'.comp
    ((coordinates F).continuous.prodMk continuous_const)).measurable

theorem frameCoefficient_norm_sq (m : PhaseSheets F ζ hζ U)
    (p : Space (KPCuspLogShape.dimension F * 3)) :
    ENNReal.ofReal (‖frameCoefficient F ζ hζ U R P H f.val i m p‖ ^ 2) =
      KPContSectorFixedLineNormIntegrals.lineNorm F ζ hζ U R P H f.val
        (basePoint F ζ hζ U R P H i p) := by
  obtain ⟨ε, rfl⟩ := QuotientGroup.mk'_surjective (centralLevel F ζ hζ U) m
  change ENNReal.ofReal (‖frameCoefficient F ζ hζ U R P H f.val i (phaseClass F ζ hζ U ε) p‖ ^ 2) = _
  rw [frameCoefficient_class, norm_mul, Circle.norm_coe, one_mul]
  exact (kp_cont_sector_fixed_line_norm_integrals F ζ hζ U R P H f.val f.property.1).component i _ |>.symm

theorem frameCoefficient_weighted_memLp (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x) (m : PhaseSheets F ζ hζ U) :
    MemLp (frameCoefficient F ζ hζ U R P H f.val i m) 2 (chartMeasure F ζ hζ U R P H i x O) := by
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)
    (frameCoefficient_measurable F ζ hζ U R P H f i m).aestronglyMeasurable]
  have he : (fun p => ‖frameCoefficient F ζ hζ U R P H f.val i m p‖ₑ ^ (2 : ℝ≥0∞).toReal) =
    fun p => KPContSectorFixedLineNormIntegrals.lineNorm F ζ hζ U R P H f.val
      (basePoint F ζ hζ U R P H i p) := by
    funext p
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two,
      ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    exact frameCoefficient_norm_sq F ζ hζ U R P H f i m p
  rw [he, ← lintegral_map
    (kp_cont_sector_fixed_line_norm_integrals F ζ hζ U R P H f.val f.property.1).borel
    (basePoint_measurable F ζ hζ U R P H i), quotient_measure]
  have ht := (borelS F ζ hζ U R P H f).property.2
  change (∫⁻ b, KPContSectorFixedLineNormIntegrals.lineNorm F ζ hζ U R P H f.val b
    ∂KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U) < ⊤ at ht
  apply lt_of_le_of_lt _ ht
  exact MeasureTheory.lintegral_mono' Measure.restrict_le_self le_rfl

end

theorem ball_measure_domination (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x)
    (A : LocalBall (KPCuspLogShape.dimension F * 3))
    (hA : KPContLocalCubeEmbedding.closedCarrier A ⊆ chartDomain F ζ hζ U R P H i x O) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ volume.restrict A.carrier ≤
      c • (chartMeasure F ζ hζ U R P H i x O).restrict A.carrier := by
  obtain ⟨a,b,ha,hab⟩ := density_bounds F A
  let k := (H.disintegration U).componentWeight i /
    (isotropyOrder F ζ hζ U R P H i x : ℝ≥0∞)
  have hk0 : k ≠ 0 := ENNReal.div_ne_zero.mpr
    ⟨ne_of_gt ((H.disintegration U).positive_componentWeight i), ENNReal.natCast_ne_top _⟩
  have hktop : k ≠ ⊤ := ENNReal.div_ne_top
    ((H.disintegration U).finite_componentWeight i).ne
    (by exact_mod_cast (isotropyOrder_pos F ζ hζ U R P H i x O).ne')
  have hAD : A.carrier ⊆ chartDomain F ζ hζ U R P H i x O := Metric.ball_subset_closedBall.trans hA
  have hAmeas : MeasurableSet A.carrier := Metric.isOpen_ball.measurableSet
  have heq : (chartMeasure F ζ hζ U R P H i x O).restrict A.carrier =
      k • (volume.restrict A.carrier).withDensity (fun p => ENNReal.ofReal (density F p)) := by
    rw [chartMeasure, Measure.restrict_smul, restrict_withDensity hAmeas,
      Measure.restrict_restrict_of_subset hAD]
  have hlow : (ENNReal.ofReal a) • volume.restrict A.carrier ≤
      (volume.restrict A.carrier).withDensity (fun p => ENNReal.ofReal (density F p)) := by
    rw [← withDensity_const]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem hAmeas] with p hp
    exact ENNReal.ofReal_le_ofReal (hab p (Metric.ball_subset_closedBall hp)).1
  have ha0 := ne_of_gt (ENNReal.ofReal_pos.mpr ha)
  refine ⟨(ENNReal.ofReal a)⁻¹ * k⁻¹, ENNReal.mul_ne_top
    (ENNReal.inv_ne_top.mpr ha0) (ENNReal.inv_ne_top.mpr hk0), ?_⟩
  rw [heq, ← smul_smul, smul_smul k⁻¹ k, ENNReal.inv_mul_cancel hk0 hktop, one_smul]
  calc
    volume.restrict A.carrier = (ENNReal.ofReal a)⁻¹ • (ENNReal.ofReal a) •
        volume.restrict A.carrier := by
      rw [smul_smul, ENNReal.inv_mul_cancel ha0 ENNReal.ofReal_ne_top, one_smul]
    _ ≤ _ := smul_le_smul_left (ENNReal.ofReal a)⁻¹ hlow

theorem frameCoefficient_memLp (f : BorelL2Scalars F ζ hζ U R)
    (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x) (m : PhaseSheets F ζ hζ U)
    (A : LocalBall (KPCuspLogShape.dimension F * 3))
    (hA : KPContLocalCubeEmbedding.closedCarrier A ⊆ chartDomain F ζ hζ U R P H i x O) :
    MemLp (frameCoefficient F ζ hζ U R P H f.val i m) 2 (volume.restrict A.carrier) := by
  obtain ⟨c,hc,hdom⟩ := ball_measure_domination F ζ hζ U R P H i x O A hA
  exact MemLp.of_measure_le_smul hc hdom
    ((frameCoefficient_weighted_memLp F ζ hζ U R P H f i x O m).restrict A.carrier)

theorem frameCoefficient_ae_eq (f g : BorelL2Scalars F ζ hζ U R)
    (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x) (m : PhaseSheets F ζ hζ U)
    (A : LocalBall (KPCuspLogShape.dimension F * 3))
    (hA : KPContLocalCubeEmbedding.closedCarrier A ⊆ chartDomain F ζ hζ U R P H i x O)
    (hfg : scalarEmbedding F ζ hζ U R P H f = scalarEmbedding F ζ hζ U R P H g) :
    frameCoefficient F ζ hζ U R P H f.val i m =ᵐ[volume.restrict A.carrier]
      frameCoefficient F ζ hζ U R P H g.val i m := by
  have hmk : mk F ζ hζ U R P H (borelS F ζ hζ U R P H f) =
      mk F ζ hζ U R P H (borelS F ζ hζ U R P H g) := by
    rw [← sectorLineIsometry_toSector, ← sectorLineIsometry_toSector]
    exact congrArg (sectorLineIsometry F ζ hζ U R P H) hfg
  have hn := (mk_eq_mk_iff F ζ hζ U R P H _ _).mp hmk
  change squaredNorm F ζ hζ U R P H (S F ζ hζ U R P H f.val - S F ζ hζ U R P H g.val) =ᵐ[
    KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U] 0 at hn
  rw [← map_sub] at hn
  have ht : Measure.QuasiMeasurePreserving (basePoint F ζ hζ U R P H i)
      (chartMeasure F ζ hζ U R P H i x O)
      (KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U) := by
    refine ⟨basePoint_measurable F ζ hζ U R P H i, ?_⟩
    rw [quotient_measure]
    exact Measure.absolutelyContinuous_of_le Measure.restrict_le_self
  have he : ∀ p, squaredNorm F ζ hζ U R P H (S F ζ hζ U R P H (f.val - g.val))
      (basePoint F ζ hζ U R P H i p) =
      ENNReal.ofReal (‖frameCoefficient F ζ hζ U R P H (f-g).val i m p‖ ^ 2) := fun p => (frameCoefficient_norm_sq F ζ hζ U R P H (f-g) i m p).symm
  have hlin : ∀ p, frameCoefficient F ζ hζ U R P H (f-g).val i m p =
      frameCoefficient F ζ hζ U R P H f.val i m p - frameCoefficient F ζ hζ U R P H g.val i m p := by
    obtain ⟨ε, rfl⟩ := QuotientGroup.mk'_surjective (centralLevel F ζ hζ U) m
    intro p
    change frameCoefficient F ζ hζ U R P H (f-g).val i (phaseClass F ζ hζ U ε) p =
      frameCoefficient F ζ hζ U R P H f.val i (phaseClass F ζ hζ U ε) p -
      frameCoefficient F ζ hζ U R P H g.val i (phaseClass F ζ hζ U ε) p
    rw [frameCoefficient_class, frameCoefficient_class, frameCoefficient_class]
    change (chi F ζ hζ ε : ℂ) * (S F ζ hζ U R P H (f.val-g.val) i).val (coordinates F p) = _
    rw [map_sub]
    exact mul_sub _ _ _
  filter_upwards [(((ht.ae hn).filter_mono (Measure.absolutelyContinuous_of_le
    (Measure.restrict_le_self)).ae_le).filter_mono (null_sets F ζ hζ U R P H i x O A hA).2.ae_le)] with p hp
  rw [he, hlin] at hp
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm (ENNReal.ofReal_eq_zero.mp hp) (sq_nonneg _))))

theorem frameCoefficient_weighted_eLpNorm_le (f : BorelL2Scalars F ζ hζ U R)
    (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x) (m : PhaseSheets F ζ hζ U) :
    eLpNorm (frameCoefficient F ζ hζ U R P H f.val i m) 2
      (chartMeasure F ζ hζ U R P H i x O) ≤
        ENNReal.ofReal ‖scalarEmbedding F ζ hζ U R P H f‖ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
    (frameCoefficient_weighted_memLp F ζ hζ U R P H f i x O m).aestronglyMeasurable]
  have he : (fun p => ‖frameCoefficient F ζ hζ U R P H f.val i m p‖ₑ ^ (2 : ℝ≥0∞).toReal) =
      fun p => KPContSectorFixedLineNormIntegrals.lineNorm F ζ hζ U R P H f.val
        (basePoint F ζ hζ U R P H i p) := by
    funext p
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two, ← ofReal_norm,
      ← ENNReal.ofReal_pow (norm_nonneg _)]
    exact frameCoefficient_norm_sq F ζ hζ U R P H f i m p
  rw [he, ← lintegral_map
    (kp_cont_sector_fixed_line_norm_integrals F ζ hζ U R P H f.val f.property.1).borel
    (basePoint_measurable F ζ hζ U R P H i), quotient_measure]
  have hle : (∫⁻ b in baseChartImage F ζ hζ U R P H i x O,
      KPContSectorFixedLineNormIntegrals.lineNorm F ζ hζ U R P H f.val b
      ∂KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U) ≤
      normIntegral F ζ hζ U R P H (borelS F ζ hζ U R P H f).val :=
    MeasureTheory.lintegral_mono' Measure.restrict_le_self le_rfl
  let scalarEmbedding₀ := scalarEmbedding F ζ hζ U R P H f
  have hnorm : normIntegral F ζ hζ U R P H (borelS F ζ hζ U R P H f).val =
      ENNReal.ofReal (‖scalarEmbedding₀‖ ^ 2) := by
    rw [← ofReal_norm_sq, ← sectorLineIsometry_toSector,
      LinearIsometryEquiv.norm_map]
    rfl
  rw [hnorm] at hle
  have hr := ENNReal.rpow_le_rpow hle (show (0 : ℝ) ≤ 1 / (2 : ℝ≥0∞).toReal by norm_num)
  have hroot : ENNReal.ofReal (‖scalarEmbedding₀‖ ^ 2) ^
      (1 / (2 : ℝ≥0∞).toReal) = ENNReal.ofReal ‖scalarEmbedding₀‖ := by
    rw [ENNReal.toReal_ofNat, ENNReal.ofReal_rpow_of_nonneg
      (sq_nonneg ‖scalarEmbedding₀‖) (show (0 : ℝ) ≤ 1/2 by norm_num),
      ← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _)]
  rw [hroot] at hr
  exact hr

theorem frameCoefficient_norm_bound (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x) (m : PhaseSheets F ζ hζ U)
    (A : LocalBall (KPCuspLogShape.dimension F * 3))
    (hA : KPContLocalCubeEmbedding.closedCarrier A ⊆ chartDomain F ζ hζ U R P H i x O) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : BorelL2Scalars F ζ hζ U R,
      ‖(frameCoefficient_memLp F ζ hζ U R P H f i x O m A hA).toLp
        (frameCoefficient F ζ hζ U R P H f.val i m)‖ ≤
          C * ‖scalarEmbedding F ζ hζ U R P H f‖ := by
  obtain ⟨c,hc,hdom⟩ := ball_measure_domination F ζ hζ U R P H i x O A hA
  let d := c ^ (1 / (2 : ℝ≥0∞).toReal)
  refine ⟨d.toReal + 1, by positivity, ?_⟩
  intro f
  let frameCoefficient₀ := frameCoefficient F ζ hζ U R P H f.val i m
  have hle := eLpNorm_le_of_measure_le_smul (f := frameCoefficient₀)
    (p := (2 : ℝ≥0∞)) hdom
  have hl : eLpNorm (frameCoefficient₀) 2
      (volume.restrict A.carrier) ≤ d * ENNReal.ofReal ‖scalarEmbedding F ζ hζ U R P H f‖ := by
    have hdEq : c ^ (1 / (2 : ℝ≥0∞)).toReal = d := by
      dsimp [d]; norm_num
    rw [hdEq] at hle
    exact hle.trans (mul_le_mul_right ((eLpNorm_mono_measure (frameCoefficient₀)
      (Measure.restrict_le_self)).trans
        (frameCoefficient_weighted_eLpNorm_le F ζ hζ U R P H f i x O m)) d)
  rw [Lp.norm_toLp]
  have ht := ENNReal.toReal_mono (ENNReal.mul_ne_top ((ENNReal.rpow_lt_top_of_nonneg (by norm_num) hc).ne) ENNReal.ofReal_ne_top) hl
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _)] at ht
  nlinarith [norm_nonneg (scalarEmbedding F ζ hζ U R P H f)]

theorem scalarEmbedding_surjective : Function.Surjective (scalarEmbedding F ζ hζ U R P H) := by
  intro u
  obtain ⟨g, hg, hgLp, f, hf, hfLp, hfU, hgen⟩ :=
    KPContSectorExactBorelRepresentatives.exists_exact_borel_representative F ζ hζ R U u
  let f' : BorelL2Scalars F ζ hζ U R := ⟨⟨f,hgen⟩,hf,hfLp⟩
  refine ⟨f', ?_⟩
  apply Subtype.ext
  rw [scalarEmbedding_coe]
  exact hfU

 def exactRepresentative (u : KPContSectorClosedLpSubspace.H F ζ hζ R U) :
    BorelL2Scalars F ζ hζ U R :=
  Classical.choose (scalarEmbedding_surjective F ζ hζ U R P H u)

 theorem exactRepresentative_spec (u : KPContSectorClosedLpSubspace.H F ζ hζ R U) :
    scalarEmbedding F ζ hζ U R P H (exactRepresentative F ζ hζ U R P H u) = u :=
  Classical.choose_spec (scalarEmbedding_surjective F ζ hζ U R P H u)

section

variable (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x) (m : PhaseSheets F ζ hζ U)
    (A : LocalBall (KPCuspLogShape.dimension F * 3))
    (hA : KPContLocalCubeEmbedding.closedCarrier A ⊆ chartDomain F ζ hζ U R P H i x O)

def representativeL2
    (f : BorelL2Scalars F ζ hζ U R) : BallL2 A :=
  (frameCoefficient_memLp F ζ hζ U R P H f i x O m A hA).toLp
    (frameCoefficient F ζ hζ U R P H f.val i m)

 theorem representativeL2_ae
    (f : BorelL2Scalars F ζ hζ U R) :
    representativeL2 F ζ hζ U R P H i x O m A hA f =ᵐ[volume.restrict A.carrier]
      frameCoefficient F ζ hζ U R P H f.val i m :=
  MemLp.coeFn_toLp _

 theorem representativeL2_eq
    (f g : BorelL2Scalars F ζ hζ U R)
    (hfg : scalarEmbedding F ζ hζ U R P H f = scalarEmbedding F ζ hζ U R P H g) :
    representativeL2 F ζ hζ U R P H i x O m A hA f =
      representativeL2 F ζ hζ U R P H i x O m A hA g := by
  apply Lp.ext
  exact (representativeL2_ae F ζ hζ U R P H i x O m A hA f).trans
    ((frameCoefficient_ae_eq F ζ hζ U R P H f g i x O m A hA hfg).trans
      (representativeL2_ae F ζ hζ U R P H i x O m A hA g).symm)

end

 theorem coefficient_add (f g : BorelL2Scalars F ζ hζ U R)
    (i : Fin (H.atlas U).componentCount) (m : PhaseSheets F ζ hζ U)
    (p : Space (KPCuspLogShape.dimension F * 3)) :
    frameCoefficient F ζ hζ U R P H (f+g).val i m p =
      frameCoefficient F ζ hζ U R P H f.val i m p + frameCoefficient F ζ hζ U R P H g.val i m p := by
  obtain ⟨ε, rfl⟩ := QuotientGroup.mk'_surjective (centralLevel F ζ hζ U) m
  change frameCoefficient F ζ hζ U R P H (f+g).val i (phaseClass F ζ hζ U ε) p =
    frameCoefficient F ζ hζ U R P H f.val i (phaseClass F ζ hζ U ε) p +
    frameCoefficient F ζ hζ U R P H g.val i (phaseClass F ζ hζ U ε) p
  rw [frameCoefficient_class, frameCoefficient_class, frameCoefficient_class]
  change (chi F ζ hζ ε : ℂ) * (S F ζ hζ U R P H (f.val+g.val) i).val (coordinates F p) = _
  rw [map_add]
  exact mul_add _ _ _

 theorem coefficient_smul (a : ℂ) (f : BorelL2Scalars F ζ hζ U R)
    (i : Fin (H.atlas U).componentCount) (m : PhaseSheets F ζ hζ U)
    (p : Space (KPCuspLogShape.dimension F * 3)) :
    frameCoefficient F ζ hζ U R P H (a • f).val i m p =
      a * frameCoefficient F ζ hζ U R P H f.val i m p := by
  obtain ⟨ε, rfl⟩ := QuotientGroup.mk'_surjective (centralLevel F ζ hζ U) m
  change frameCoefficient F ζ hζ U R P H (a • f).val i (phaseClass F ζ hζ U ε) p =
    a * frameCoefficient F ζ hζ U R P H f.val i (phaseClass F ζ hζ U ε) p
  rw [frameCoefficient_class, frameCoefficient_class]
  change (chi F ζ hζ ε : ℂ) * (S F ζ hζ U R P H (a • f.val) i).val (coordinates F p) = _
  rw [map_smul]
  change (chi F ζ hζ ε : ℂ) * (a * (S F ζ hζ U R P H f.val i).val (coordinates F p)) = _
  ring

 section

variable (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x) (m : PhaseSheets F ζ hζ U)
    (A : LocalBall (KPCuspLogShape.dimension F * 3))
    (hA : KPContLocalCubeEmbedding.closedCarrier A ⊆ chartDomain F ζ hζ U R P H i x O)

def restrictionLinear :
    KPContSectorClosedLpSubspace.H F ζ hζ R U →ₗ[ℂ] BallL2 A where
  toFun u := representativeL2 F ζ hζ U R P H i x O m A hA (exactRepresentative F ζ hζ U R P H u)
  map_add' u v := by
    let exactRepresentative₀ := exactRepresentative F ζ hζ U R P H
    rw [representativeL2_eq F ζ hζ U R P H i x O m A hA
      (exactRepresentative₀ (u+v))
      (exactRepresentative₀ u + exactRepresentative₀ v)
      (by rw [map_add, exactRepresentative_spec, exactRepresentative_spec, exactRepresentative_spec])]
    apply Lp.ext
    filter_upwards [representativeL2_ae F ζ hζ U R P H i x O m A hA
      (exactRepresentative₀ u + exactRepresentative₀ v),
      Lp.coeFn_add (representativeL2 F ζ hζ U R P H i x O m A hA (exactRepresentative₀ u))
        (representativeL2 F ζ hζ U R P H i x O m A hA (exactRepresentative₀ v)),
      representativeL2_ae F ζ hζ U R P H i x O m A hA (exactRepresentative₀ u),
      representativeL2_ae F ζ hζ U R P H i x O m A hA (exactRepresentative₀ v)] with p hp hsum hu hv
    rw [hp, hsum]
    simp only [Pi.add_apply, hu, hv, coefficient_add]
  map_smul' a u := by
    let exactRepresentative₀ := exactRepresentative F ζ hζ U R P H
    rw [representativeL2_eq F ζ hζ U R P H i x O m A hA
      (exactRepresentative₀ (a • u)) (a • exactRepresentative₀ u)
      (by rw [map_smul, exactRepresentative_spec, exactRepresentative_spec])]
    apply Lp.ext
    filter_upwards [representativeL2_ae F ζ hζ U R P H i x O m A hA
      (a • exactRepresentative₀ u),
      Lp.coeFn_smul a (representativeL2 F ζ hζ U R P H i x O m A hA (exactRepresentative₀ u)),
      representativeL2_ae F ζ hζ U R P H i x O m A hA (exactRepresentative₀ u)] with p hp hs hu
    simp only [RingHom.id_apply]
    rw [hp, hs]
    simp only [Pi.smul_apply, smul_eq_mul, hu, coefficient_smul]

def restriction :
    KPContSectorClosedLpSubspace.H F ζ hζ R U →L[ℂ] BallL2 A :=
  (restrictionLinear F ζ hζ U R P H i x O m A hA).mkContinuousOfExistsBound (by
    obtain ⟨C,hC,hbound⟩ := frameCoefficient_norm_bound F ζ hζ U R P H i x O m A hA
    exact ⟨C, fun u => by simpa only [restrictionLinear, LinearMap.coe_mk, AddHom.coe_mk,
      representativeL2, exactRepresentative_spec] using hbound (exactRepresentative F ζ hζ U R P H u)⟩)

theorem restriction_representative
    (u : KPContSectorClosedLpSubspace.H F ζ hζ R U) (f : BorelL2Scalars F ζ hζ U R)
    (hf : scalarEmbedding F ζ hζ U R P H f = u) :
    restriction F ζ hζ U R P H i x O m A hA u =ᵐ[volume.restrict A.carrier]
      frameCoefficient F ζ hζ U R P H f.val i m := by
  change representativeL2 F ζ hζ U R P H i x O m A hA (exactRepresentative F ζ hζ U R P H u) =ᵐ[_] _
  rw [representativeL2_eq F ζ hζ U R P H i x O m A hA _ f
    ((exactRepresentative_spec F ζ hζ U R P H u).trans hf.symm)]
  exact representativeL2_ae F ζ hζ U R P H i x O m A hA f

end

theorem restriction_smaller_ball (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x) (m : PhaseSheets F ζ hζ U)
    (A B : LocalBall (KPCuspLogShape.dimension F * 3))
    (hA : KPContLocalCubeEmbedding.closedCarrier A ⊆ chartDomain F ζ hζ U R P H i x O)
    (hB : KPContLocalCubeEmbedding.closedCarrier B ⊆ chartDomain F ζ hζ U R P H i x O)
    (hAB : A.carrier ⊆ B.carrier) (u : KPContSectorClosedLpSubspace.H F ζ hζ R U) :
    ∀ᵐ p ∂volume.restrict A.carrier,
      restriction F ζ hζ U R P H i x O m A hA u p =
        restriction F ζ hζ U R P H i x O m B hB u p := by
  let f := exactRepresentative F ζ hζ U R P H u
  exact (restriction_representative F ζ hζ U R P H i x O m A hA u f
    (exactRepresentative_spec F ζ hζ U R P H u)).trans ((restriction_representative F ζ hζ U R P H i x O m B hB u f
    (exactRepresentative_spec F ζ hζ U R P H u)).filter_mono
    (Measure.absolutelyContinuous_of_le (Measure.restrict_mono hAB le_rfl)).ae_le).symm

theorem restriction_overlap (i : Fin (H.atlas U).componentCount) (x y : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x) (O' : OrbifoldChart F ζ hζ U R P H i y)
    (m m' : PhaseSheets F ζ hζ U) (ε : rootsOfUnity 3 F)
    (γ : Component F ζ hζ U R P H i) (A B : LocalBall (KPCuspLogShape.dimension F * 3))
    (hA : KPContLocalCubeEmbedding.closedCarrier A ⊆ chartDomain F ζ hζ U R P H i x O)
    (hB : KPContLocalCubeEmbedding.closedCarrier B ⊆ chartDomain F ζ hζ U R P H i y O')
    (hm : m = phaseClass F ζ hζ U ε * m') (u : KPContSectorClosedLpSubspace.H F ζ hζ R U) :
    ∀ᵐ p ∂volume.restrict (A.carrier ∩ overlapCoordinate F ζ hζ U R P H i γ ⁻¹' B.carrier),
      restriction F ζ hζ U R P H i x O m A hA u p =
        (overlapTransition F ζ hζ U R P H i γ ε : ℂ) *
          restriction F ζ hζ U R P H i y O' m' B hB u (overlapCoordinate F ζ hζ U R P H i γ p) := by
  let f := exactRepresentative F ζ hζ U R P H u
  filter_upwards [((restriction_representative F ζ hζ U R P H i x O m A hA u f
    (exactRepresentative_spec F ζ hζ U R P H u)).filter_mono (Measure.absolutelyContinuous_of_le
    (Measure.restrict_mono
      Set.inter_subset_left le_rfl)).ae_le), (((overlapCoordinate_quasiMeasurePreserving F ζ hζ U R P H i γ).ae ((ae_restrict_iff' Metric.isOpen_ball.measurableSet).mp (restriction_representative F ζ hζ U R P H i y O' m' B hB u f
    (exactRepresentative_spec F ζ hζ U R P H u)))).filter_mono (Measure.absolutelyContinuous_of_le
    (Measure.restrict_le_self)).ae_le), ae_restrict_mem (Metric.isOpen_ball.measurableSet.inter
    ((overlapCoordinate_quasiMeasurePreserving F ζ hζ U R P H i γ).measurable Metric.isOpen_ball.measurableSet))] with p hp htp hmem
  rw [hp, htp hmem.2]
  exact frameCoefficient_overlap F ζ hζ U R P H f.val i m m' ε γ hm p

structure RestrictionFamily where
  restriction : ∀ (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x) (m : PhaseSheets F ζ hζ U)
    (A : LocalBall (KPCuspLogShape.dimension F * 3)),
    KPContLocalCubeEmbedding.closedCarrier A ⊆ chartDomain F ζ hζ U R P H i x O →
    KPContSectorClosedLpSubspace.H F ζ hζ R U →L[ℂ] BallL2 A

  bound : ∀ (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x) (m : PhaseSheets F ζ hζ U)
    (A : LocalBall (KPCuspLogShape.dimension F * 3))
    (hA : KPContLocalCubeEmbedding.closedCarrier A ⊆ chartDomain F ζ hζ U R P H i x O),
    ∃ c : ℝ, 0 < c ∧ ∀ u, ‖restriction i x O m A hA u‖ ≤ c * ‖u‖

  stabilizer : ∀ (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x) (m : PhaseSheets F ζ hζ U)
    (A : LocalBall (KPCuspLogShape.dimension F * 3))
    (hA : KPContLocalCubeEmbedding.closedCarrier A ⊆ chartDomain F ζ hζ U R P H i x O)
    (σ : MulAction.stabilizer (Component F ζ hζ U R P H i) x) (u : KPContSectorClosedLpSubspace.H F ζ hζ R U),
    ∀ᵐ p ∂volume.restrict (A.carrier ∩ overlapCoordinate F ζ hζ U R P H i σ.val ⁻¹' A.carrier),
      restriction i x O m A hA u (overlapCoordinate F ζ hζ U R P H i σ.val p) =
        (chi F ζ hζ (((H.atlas U).line i).rho σ.val) : ℂ) * restriction i x O m A hA u p

def restrictionFamily : RestrictionFamily F ζ hζ U R P H where
  restriction := restriction F ζ hζ U R P H
  bound i x O m A hA := by
    obtain ⟨C,hC,hb⟩ := frameCoefficient_norm_bound F ζ hζ U R P H i x O m A hA
    refine ⟨C,hC,fun u => ?_⟩
    change ‖representativeL2 F ζ hζ U R P H i x O m A hA (exactRepresentative F ζ hζ U R P H u)‖ ≤ C * ‖u‖
    simpa only [representativeL2, exactRepresentative_spec] using hb (exactRepresentative F ζ hζ U R P H u)
  stabilizer i x O m A hA σ u := by
    have ho := restriction_overlap F ζ hζ U R P H i x x O O m m 1 σ.val A A hA hA
      (by simp) u
    filter_upwards [ho] with p hp
    have ht : (overlapTransition F ζ hζ U R P H i σ.val 1 : ℂ) =
        (chi F ζ hζ (((H.atlas U).line i).rho σ.val) : ℂ)⁻¹ := by
      simp [overlapTransition, map_inv]
    rw [ht] at hp
    have hne : (chi F ζ hζ (((H.atlas U).line i).rho σ.val) : ℂ) ≠ 0 := Circle.coe_ne_zero _
    have h := congrArg (fun z : ℂ => (chi F ζ hζ (((H.atlas U).line i).rho σ.val) : ℂ) * z) hp
    simpa only [← mul_assoc, mul_inv_cancel₀ hne, one_mul] using h.symm

end DedekindZetaZeroFree.KPContActualChartRestrictionDensity

namespace DedekindZetaZeroFree

theorem kp_cont_actual_chart_restriction_density
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (_actual : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H) :
    KPContActualChartRestrictionDensity.DensityIdentities F ζ hζ U R P H ∧
      Nonempty (KPContActualChartRestrictionDensity.RestrictionFamily F ζ hζ U R P H) := ⟨KPContActualChartRestrictionDensity.densityIdentities F ζ hζ U R P H,
    ⟨KPContActualChartRestrictionDensity.restrictionFamily F ζ hζ U R P H⟩⟩

end DedekindZetaZeroFree

end
