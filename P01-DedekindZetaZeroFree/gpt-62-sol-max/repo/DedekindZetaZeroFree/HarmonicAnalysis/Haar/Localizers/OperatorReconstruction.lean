module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.HaarLocalizers.LineRestriction
public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.CuspCoordinatesAndTruncation

@[expose] public section

set_option maxHeartbeats 2400000
noncomputable section
open scoped Classical NumberField ENNReal
open MeasureTheory Topology
namespace DedekindZetaZeroFree.KPFixedHaarLocalizersBodies

open KPContActualFixedHaarCoreLocalizers KPContSectorSmoothFramesSupport KPContSectorLineL2Isometry
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

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

open scoped InnerProductSpace Matrix
open HyperbolicChart








theorem componentWeight_toReal_pos (i : Fin (H.atlas U).componentCount) :
    0 < ((H.disintegration U).componentWeight i).toReal :=
  ENNReal.toReal_pos (ne_of_gt ((H.disintegration U).positive_componentWeight i))
    (ne_of_lt ((H.disintegration U).finite_componentWeight i))

theorem actualWeight_bounds (C : Chart F ζ hζ U R P H) :
    0 < ((H.disintegration U).componentWeight C.component).toReal * C.lower ∧
    ∀ x ∈ closure (Metric.ball (0 : CoreChartLocalizers.E C.n) C.radius),
      ((H.disintegration U).componentWeight C.component).toReal * C.lower ≤
        actualWeight F ζ hζ U R P H C x ∧
      actualWeight F ζ hζ U R P H C x ≤
        ((H.disintegration U).componentWeight C.component).toReal * C.upper := by
  have hc := componentWeight_toReal_pos F ζ hζ U R P H C.component
  refine ⟨mul_pos hc C.positive_lower, ?_⟩
  intro x hx
  exact ⟨mul_le_mul_of_nonneg_left (C.finite_bounds x hx).1 hc.le,
    mul_le_mul_of_nonneg_left (C.finite_bounds x hx).2 hc.le⟩


theorem average_cutoff_section
    (C : Chart F ζ hζ U R P H) (η : CoreChartLocalizers.E C.n → ℝ)
    (hη : ∀ (g : C.G F ζ hζ H.totallyComplex U) x, η (C.orthogonal g x) = η x)
    (s : Sections F ζ hζ U R P H) {x : CoreChartLocalizers.E C.n}
    (hx : x ∈ Metric.ball 0 C.radius) :
    ((KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).orthogonalProjectionOnto
      (C.average F ζ hζ H.totallyComplex U
        (fun y => (η y : ℂ) * (s C.component).val (C.coordinates y)) x) : ℂ) =
      (η x : ℂ) * (s C.component).val (C.coordinates x) := by
  have heq : ∀ (g : C.G F ζ hζ H.totallyComplex U) y,
      y ∈ Metric.ball 0 C.radius →
      (η (C.orthogonal g y) : ℂ) * (s C.component).val (C.coordinates (C.orthogonal g y)) =
        (C.rho F ζ hζ H.totallyComplex U g : ℂ) *
          ((η y : ℂ) * (s C.component).val (C.coordinates y)) := by
    intro g y hy
    rw [hη, C.equivariance g y (C.closed_ball_in_extension (subset_closure hy))]
    have hs := (s C.component).property.2 g.val (C.coordinates y)
    rw [hs]
    simp only [CoreChartLocalizers.Chart.rho, MonoidHom.comp_apply, Subgroup.subtype_apply]
    ring
  rw [C.average_eq_self F ζ hζ H.totallyComplex U _ heq hx]
  let v : KPCuspGenuineMonodromy.scalarFiber F ζ hζ U :=
    ⟨(η x : ℂ) * (s C.component).val (C.coordinates x),
      (KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).smul_mem (η x : ℂ)
        ((s C.component).property.1 (C.coordinates x))⟩
  exact congrArg Subtype.val
    ((KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).orthogonalProjectionOnto_mem_subspace_eq_self v)

 def mulSections (φ : X_U F ζ hζ U → ℝ) (s : Sections F ζ hζ U R P H) :
    Sections F ζ hζ U R P H := fun i =>
  ⟨fun x => (φ ((H.atlas U).components ⟨i, Quotient.mk _ x⟩) : ℂ) * (s i).val x,
    (by intro x; exact (KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).smul_mem _ ((s i).property.1 x)),
    (by
      intro γ x
      have hq : (Quotient.mk _ ((γ : KPCuspArithmetic.PGL2 F) • x) :
          KPCuspSiegel.OrbitQuotient F (KPCuspGenuineMonodromy.Component F ζ hζ U
            ((H.atlas U).representative i))) = Quotient.mk _ x :=
        (Quotient.sound (MulAction.orbitRel_apply.mpr
          (MulAction.mem_orbit_iff.mpr ⟨γ⁻¹, inv_smul_smul γ x⟩))).symm
      dsimp only
      rw [hq, (s i).property.2 γ x]
      ring)⟩

 theorem mulSections_norm (φ : X_U F ζ hζ U → ℝ) (s : Sections F ζ hζ U R P H)
    (b : X_U F ζ hζ U) :
    sectionNorm F ζ hζ U R P H (mulSections F ζ hζ U R P H φ s) b =
      |φ b| * sectionNorm F ζ hζ U R P H s b := by
  obtain ⟨⟨i,q⟩,rfl⟩ := (H.atlas U).components.surjective b
  refine Quotient.inductionOn q fun x => ?_
  rw [sectionNorm_component, sectionNorm_component]
  exact (norm_mul _ _).trans (by rw [Complex.norm_real, Real.norm_eq_abs])

 def mulBorel (φ : X_U F ζ hζ U → ℝ)
    (hφ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (fun z => φ
      (KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative j)
        (KPCuspSiegel.projection F _ z))))
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ b, |φ b| ≤ M)
    (s : BorelL2Sections F ζ hζ U R P H) : BorelL2Sections F ζ hζ U R P H := by
  refine ⟨mulSections F ζ hζ U R P H φ s.val, ?_, ?_⟩
  · intro i
    have hm : Measurable (fun x => φ ((H.atlas U).components ⟨i,Quotient.mk _ x⟩)) := by
      convert (hφ i).continuous.measurable using 1
      funext x
      rw [(H.atlas U).components_formula]
      rfl
    exact hm.complex_ofReal.mul (s.property.1 i)
  · unfold normIntegral squaredNorm
    have he : ∀ b, ENNReal.ofReal (sectionNorm F ζ hζ U R P H
        (mulSections F ζ hζ U R P H φ s.val) b ^ 2) ≤
        ENNReal.ofReal (M^2) * squaredNorm F ζ hζ U R P H s.val b := by
      intro b
      rw [mulSections_norm, mul_pow, ENNReal.ofReal_mul (sq_nonneg _)]
      exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (abs_nonneg _) (hbound b) 2)) _
    apply (lintegral_mono he).trans_lt
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top s.property.2

private theorem sectionNorm_nonneg (s : Sections F ζ hζ U R P H)
    (b : X_U F ζ hζ U) : 0 ≤ sectionNorm F ζ hζ U R P H s b := by
  dsimp [sectionNorm]
  refine Quotient.inductionOn ((H.atlas U).components.symm b).2 (fun x => ?_)
  exact norm_nonneg _

private theorem norm_difference_le (s t : Sections F ζ hζ U R P H) (b : X_U F ζ hζ U) :
    sectionNorm F ζ hζ U R P H (s - t) b ≤
      sectionNorm F ζ hζ U R P H s b + sectionNorm F ζ hζ U R P H t b := by
  dsimp [sectionNorm]
  refine Quotient.inductionOn ((H.atlas U).components.symm b).2 (fun x => ?_)
  exact norm_sub_le _ _

private theorem squaredNorm_zero_iff (s : Sections F ζ hζ U R P H) (b : X_U F ζ hζ U) :
    squaredNorm F ζ hζ U R P H s b = 0 ↔ sectionNorm F ζ hζ U R P H s b = 0 := by
  rw [squaredNorm, ENNReal.ofReal_eq_zero]
  constructor
  · intro h
    nlinarith [sectionNorm_nonneg F ζ hζ U R P H s b]
  · intro h
    simp [h]

private theorem zero_difference (s t : Sections F ζ hζ U R P H) (b : X_U F ζ hζ U)
    (hs : squaredNorm F ζ hζ U R P H s b = 0)
    (ht : squaredNorm F ζ hζ U R P H t b = 0) :
    squaredNorm F ζ hζ U R P H (s - t) b = 0 := by
  apply (squaredNorm_zero_iff F ζ hζ U R P H _ b).mpr
  have h := norm_difference_le F ζ hζ U R P H s t b
  rw [(squaredNorm_zero_iff F ζ hζ U R P H s b).mp hs,
    (squaredNorm_zero_iff F ζ hζ U R P H t b).mp ht, zero_add] at h
  exact le_antisymm h (sectionNorm_nonneg F ζ hζ U R P H _ b)

private theorem local_null_global
    (K : Set (X_U F ζ hζ U)) (hK : MeasurableSet K)
    (C : Chart F ζ hζ U R P H)
    (hchart : Measure.map (C.toBase F ζ hζ H.totallyComplex U)
      ((Fintype.card (C.G F ζ hζ H.totallyComplex U) : ℝ≥0∞)⁻¹ •
        (volume.restrict (Metric.ball 0 C.radius)).withDensity
          (fun x => ENNReal.ofReal (actualWeight F ζ hζ U R P H C x))) =
      (muU F ζ hζ U R P).restrict (C.O F ζ hζ H.totallyComplex U))
    (s : BorelL2Sections F ζ hζ U R P H)
    (heq : ∀ᵐ x ∂volume.restrict (Metric.ball 0 C.radius),
      C.toBase F ζ hζ H.totallyComplex U x ∈ K → (s.val C.component).val (C.coordinates x) = 0)
    (hoff : ∀ᵐ b ∂(muU F ζ hζ U R P).restrict K,
      b ∉ C.O F ζ hζ H.totallyComplex U → squaredNorm F ζ hζ U R P H s.val b = 0) :
    mkK F ζ hζ U R P H K s = 0 := by
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  change squaredNorm F ζ hζ U R P H s.val =ᵐ[(muU F ζ hζ U R P).restrict K] 0
  let ν := ((Fintype.card (C.G F ζ hζ H.totallyComplex U) : ℝ≥0∞)⁻¹ •
        (volume.restrict (Metric.ball 0 C.radius)).withDensity
          (fun x => ENNReal.ofReal (actualWeight F ζ hζ U R P H C x)))
  have hν : ν ≪ volume.restrict (Metric.ball 0 C.radius) :=
    Measure.smul_absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)
  have hcoord : ∀ᵐ x ∂ν, C.toBase F ζ hζ H.totallyComplex U x ∈ K →
      squaredNorm F ζ hζ U R P H s.val (C.toBase F ζ hζ H.totallyComplex U x) = 0 := by
    filter_upwards [hν.ae_le heq] with x hx hmem
    rw [squaredNorm, CoreChartLocalizers.Chart.toBase, ← (H.atlas U).components_formula,
      KPCuspSiegel.projection, sectionNorm_component, hx hmem]
    simp
  have hm := squaredNorm_measurable F ζ hζ U R P H s.val s.property.1
  have hb : AEMeasurable (C.toBase F ζ hζ H.totallyComplex U) ν :=
    ((continuousOn_iff_continuous_restrict.mpr
      (C.toBase_ball_continuous F ζ hζ H.totallyComplex U)).aemeasurable
      Metric.isOpen_ball.measurableSet).mono_ac hν
  have hon : ∀ᵐ b ∂(muU F ζ hζ U R P).restrict (C.O F ζ hζ H.totallyComplex U),
      b ∈ K → squaredNorm F ζ hζ U R P H s.val b = 0 := by
    rw [← hchart]
    have hms : MeasurableSet {b | b ∈ K → squaredNorm F ζ hζ U R P H s.val b = 0} := by
      have he : {b | b ∈ K → squaredNorm F ζ hζ U R P H s.val b = 0} =
          Kᶜ ∪ {b | squaredNorm F ζ hζ U R P H s.val b = 0} := by
        ext b; simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff]; tauto
      rw [he]
      exact hK.compl.union (hm (measurableSet_singleton 0))
    exact (ae_map_iff hb hms).mpr hcoord
  rw [ae_restrict_iff' (C.open_image F ζ hζ H.totallyComplex U).measurableSet] at hon
  have hk := ae_restrict_mem (μ := muU F ζ hζ U R P) hK
  filter_upwards [Filter.Eventually.filter_mono ae_restrict_le hon, hoff, hk] with b hb ho hbk
  by_cases hx : b ∈ C.O F ζ hζ H.totallyComplex U
  · exact hb hx hbk
  · exact ho hx

theorem chart_reconstruction
    (K : Set (X_U F ζ hζ U)) (hK : IsCompact K) (C : Chart F ζ hζ U R P H)
    (φ : X_U F ζ hζ U → ℝ)
    (hφ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (fun z => φ
      (KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative j)
        (KPCuspSiegel.projection F _ z))))
    (hφs : tsupport φ ⊆ C.O F ζ hζ H.totallyComplex U)
    (η : CoreChartLocalizers.E C.n → ℝ)
    (hη : η = (Metric.ball 0 C.radius).indicator (fun x => φ (C.toBase F ζ hζ H.totallyComplex U x)))
    (hηinv : ∀ (g : C.G F ζ hζ H.totallyComplex U) x, η (C.orthogonal g x) = η x)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ b, |φ b| ≤ M)
    (T : H_U F ζ hζ U R →L[ℂ] Lp ℂ 2 (volume.restrict (CoreChartLocalizers.cube C.n C.a)))
    (hT : ∀ u s, sectorLineIsometry F ζ hζ U R P H u = mk F ζ hζ U R P H s →
      T u =ᵐ[volume.restrict (CoreChartLocalizers.cube C.n C.a)]
        (fun x => (η x : ℂ) * (s.val C.component).val (C.coordinates x)))
    (Rmap : Lp ℂ 2 (volume.restrict (CoreChartLocalizers.cube C.n C.a)) →L[ℂ] H_K F ζ hζ U R P H K)
    (hR : ∀ f, ∃ t : BorelL2Sections F ζ hζ U R P H, Rmap f = mkK F ζ hζ U R P H K t ∧
      (∀ᵐ x ∂volume.restrict (Metric.ball 0 C.radius), C.toBase F ζ hζ H.totallyComplex U x ∈ K →
        (t.val C.component).val (C.coordinates x) =
          ((KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).orthogonalProjectionOnto
            (C.average F ζ hζ H.totallyComplex U f x) : ℂ)) ∧
      (∀ᵐ b ∂(muU F ζ hζ U R P).restrict K, b ∉ C.O F ζ hζ H.totallyComplex U →
        squaredNorm F ζ hζ U R P H t.val b = 0))
    (hchart : Measure.map (C.toBase F ζ hζ H.totallyComplex U)
      ((Fintype.card (C.G F ζ hζ H.totallyComplex U) : ℝ≥0∞)⁻¹ •
        (volume.restrict (Metric.ball 0 C.radius)).withDensity
          (fun x => ENNReal.ofReal (actualWeight F ζ hζ U R P H C x))) =
      (muU F ζ hζ U R P).restrict (C.O F ζ hζ H.totallyComplex U))
    (u : H_U F ζ hζ U R) (s : BorelL2Sections F ζ hζ U R P H)
    (hs : sectorLineIsometry F ζ hζ U R P H u = mk F ζ hζ U R P H s) :
    Rmap (T u) = mkK F ζ hζ U R P H K (mulBorel F ζ hζ U R P H φ hφ M hM hbound s) := by
  obtain ⟨t,ht,hball,hoff⟩ := hR (T u)
  rw [ht]
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply local_null_global F ζ hζ U R P H K hK.measurableSet C hchart
  · have hsub : Metric.ball (0 : CoreChartLocalizers.E C.n) C.radius ⊆
        CoreChartLocalizers.cube C.n C.a := subset_closure.trans (C.closed_ball_in_cube.trans interior_subset)
    have ha := C.average_congr_ae F ζ hζ H.totallyComplex U
      ((hT u s hs).filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)))
    filter_upwards [hball,ha,ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx ha hxb hmem
    change (t.val C.component).val (C.coordinates x) -
      (φ ((H.atlas U).components ⟨C.component,Quotient.mk _ (C.coordinates x)⟩) : ℂ) *
        (s.val C.component).val (C.coordinates x) = 0
    rw [hx hmem,ha,average_cutoff_section F ζ hζ U R P H C η hηinv s.val hxb]
    rw [hη,Set.indicator_of_mem hxb]
    rw [(H.atlas U).components_formula]
    simp only [CoreChartLocalizers.Chart.toBase, KPCuspSiegel.projection, sub_self]
  · filter_upwards [hoff] with b hb hout
    apply zero_difference F ζ hζ U R P H _ _ b (hb hout)
    change squaredNorm F ζ hζ U R P H (mulSections F ζ hζ U R P H φ s.val) b = 0
    rw [squaredNorm,mulSections_norm]
    have hz : φ b = 0 := image_eq_zero_of_notMem_tsupport (fun h => hout (hφs h))
    simp [hz]

theorem finite_reconstruction {n : ℕ}
    (K : Set (X_U F ζ hζ U)) (hK : IsCompact K)
    (C : Fin n → Chart F ζ hζ U R P H)
    (φ : Fin n → X_U F ζ hζ U → ℝ)
    (hφ : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun z => φ i
      (KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative j)
        (KPCuspSiegel.projection F _ z))))
    (hφs : ∀ i, tsupport (φ i) ⊆ (C i).O F ζ hζ H.totallyComplex U)
    (hpart : ∀ b ∈ K, ∑ i, φ i b = 1)
    (η : ∀ i, CoreChartLocalizers.E (C i).n → ℝ)
    (hη : ∀ i, η i = (Metric.ball 0 (C i).radius).indicator
      (fun x => φ i ((C i).toBase F ζ hζ H.totallyComplex U x)))
    (hηinv : ∀ i (g : (C i).G F ζ hζ H.totallyComplex U) x, η i ((C i).orthogonal g x) = η i x)
    (M : Fin n → ℝ) (hM : ∀ i, 0 ≤ M i) (hbound : ∀ i b, |φ i b| ≤ M i)
    (T : ∀ i, H_U F ζ hζ U R →L[ℂ] Lp ℂ 2 (volume.restrict (CoreChartLocalizers.cube (C i).n (C i).a)))
    (hT : ∀ i u s, sectorLineIsometry F ζ hζ U R P H u = mk F ζ hζ U R P H s →
      T i u =ᵐ[volume.restrict (CoreChartLocalizers.cube (C i).n (C i).a)]
        (fun x => (η i x : ℂ) * (s.val (C i).component).val ((C i).coordinates x)))
    (Rmap : ∀ i, Lp ℂ 2 (volume.restrict (CoreChartLocalizers.cube (C i).n (C i).a)) →L[ℂ] H_K F ζ hζ U R P H K)
    (hR : ∀ i f, ∃ t : BorelL2Sections F ζ hζ U R P H, Rmap i f = mkK F ζ hζ U R P H K t ∧
      (∀ᵐ x ∂volume.restrict (Metric.ball 0 (C i).radius), (C i).toBase F ζ hζ H.totallyComplex U x ∈ K →
        (t.val (C i).component).val ((C i).coordinates x) =
          ((KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).orthogonalProjectionOnto
            ((C i).average F ζ hζ H.totallyComplex U f x) : ℂ)) ∧
      (∀ᵐ b ∂(muU F ζ hζ U R P).restrict K, b ∉ (C i).O F ζ hζ H.totallyComplex U →
        squaredNorm F ζ hζ U R P H t.val b = 0))
    (hchart : ∀ i, Measure.map ((C i).toBase F ζ hζ H.totallyComplex U)
      ((Fintype.card ((C i).G F ζ hζ H.totallyComplex U) : ℝ≥0∞)⁻¹ •
        (volume.restrict (Metric.ball 0 (C i).radius)).withDensity
          (fun x => ENNReal.ofReal (actualWeight F ζ hζ U R P H (C i) x))) =
      (muU F ζ hζ U R P).restrict ((C i).O F ζ hζ H.totallyComplex U)) :
    res_K F ζ hζ U R P H K hK.measurableSet = ∑ i, (Rmap i).comp (T i) := by
  apply ContinuousLinearMap.ext
  intro u
  obtain ⟨s,hs⟩ := Quotient.exists_rep (sectorLineIsometry F ζ hζ U R P H u)
  change mk F ζ hζ U R P H s = sectorLineIsometry F ζ hζ U R P H u at hs
  have hr : res_K F ζ hζ U R P H K hK.measurableSet u = mkK F ζ hζ U R P H K s := by
    change lineRestriction F ζ hζ U R P H K hK.measurableSet (sectorLineIsometry F ζ hζ U R P H u) = _
    rw [← hs,lineRestriction_mk]
  rw [hr,ContinuousLinearMap.sum_apply]
  simp only [ContinuousLinearMap.comp_apply]
  have he : ∀ i, Rmap i (T i u) = mkK F ζ hζ U R P H K
      (mulBorel F ζ hζ U R P H (φ i) (hφ i) (M i) (hM i) (hbound i) s) := fun i =>
    chart_reconstruction F ζ hζ U R P H K hK (C i) (φ i) (hφ i) (hφs i)
      (η i) (hη i) (hηinv i) (M i) (hM i) (hbound i) (T i) (hT i)
      (Rmap i) (hR i) (hchart i) u s hs.symm
  simp_rw [he]
  rw [← map_sum]
  apply (mkK_eq_iff F ζ hζ U R P H K _ _).mpr
  filter_upwards [ae_restrict_mem hK.measurableSet] with b hb
  obtain ⟨⟨j,q⟩,rfl⟩ := (H.atlas U).components.surjective b
  refine Quotient.inductionOn q (fun x => ?_) hb
  intro hx
  rw [squaredNorm,sectionNorm_component]
  have heq : (s.val j).val x = ((∑ i, (mulBorel F ζ hζ U R P H (φ i) (hφ i)
      (M i) (hM i) (hbound i) s)).val j).val x := by
    simp only [Submodule.coe_sum, Finset.sum_apply]
    change (s.val j).val x = ∑ i, (φ i ((H.atlas U).components ⟨j,Quotient.mk _ x⟩) : ℂ) * (s.val j).val x
    rw [← Finset.sum_mul,← Complex.ofReal_sum,hpart _ hx,Complex.ofReal_one,one_mul]
  change ENNReal.ofReal (‖(s.val j).val x - _‖ ^ 2) = 0
  rw [heq,sub_self]
  simp

end DedekindZetaZeroFree.KPFixedHaarLocalizersBodies

end
