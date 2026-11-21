module

public import DedekindZetaZeroFree.Metaplectic.Cubic.Quotients.FiniteOrbitIntegration
public import DedekindZetaZeroFree.Metaplectic.Cubic.LineBundles.SmoothSectionsAndSupport

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal NNReal
open MeasureTheory

namespace DedekindZetaZeroFree.KPContSectorFixedLineNormIntegrals

open KPContSectorCoveredQuotientVocabulary KPContSectorScalarLineAlgebra
open KPContSectorSmoothFramesSupport KPContSectorFixedPushforwardSupport
open KPMsFixedHaarDisintegration

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

def lineNorm (f : GenuineCoveredScalars F ζ hζ U) :
    KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ≥0∞ :=
  fun b => ENNReal.ofReal (sectionNorm F ζ hζ U R P H (S F ζ hζ U R P H f) b ^ 2)

def componentLineNorm (f : GenuineCoveredScalars F ζ hζ U)
    (i : Fin (H.atlas U).componentCount) :
    KPCuspSiegel.OrbitQuotient F
      (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i)) → ℝ≥0∞ :=
  fun x => ENNReal.ofReal
    (componentNorm F ζ hζ U R P H (S F ζ hζ U R P H f) i x ^ 2)

structure NormIdentities (f : GenuineCoveredScalars F ζ hζ U) : Prop where
  borel : Measurable (lineNorm F ζ hζ U R P H f)

  component : ∀ (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F),
    lineNorm F ζ hζ U R P H f ((H.atlas U).components ⟨i, Quotient.mk _ x⟩) =
      ENNReal.ofReal (‖(S F ζ hζ U R P H f i).val x‖ ^ 2)

  component_borel : ∀ i, Measurable (componentLineNorm F ζ hζ U R P H f i)

  restricted_pushforward : ∀ E : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U), MeasurableSet E →
    (∫⁻ v in (q F ζ hζ U) ⁻¹' E, ENNReal.ofReal (‖f.val v‖ ^ 2)
      ∂coveredMeasure F ζ hζ R U) =
    ∫⁻ b in E, lineNorm F ζ hζ U R P H f b ∂sphericalMeasure F ζ hζ R P U

  component_integral : ∀ E : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U), MeasurableSet E →
    (∫⁻ b in E, lineNorm F ζ hζ U R P H f b ∂sphericalMeasure F ζ hζ R P U) =
    ∑ i : Fin (H.atlas U).componentCount, (H.disintegration U).componentWeight i *
      ∫⁻ x in (KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative i)) ⁻¹' E,
        componentLineNorm F ζ hζ U R P H f i x
        ∂KPFiniteCuspAtlas.quotientVolume F
          (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i))
          ((H.atlas U).cuspAtlas i).fundamentalDomain

  lp_norm : ∀ hf : MemLp f.val 2 (coveredMeasure F ζ hζ R U),
    ‖hf.toLp f.val‖ ^ 2 =
      (∫⁻ b, lineNorm F ζ hζ U R P H f b ∂sphericalMeasure F ζ hζ R P U).toReal


end DedekindZetaZeroFree.KPContSectorFixedLineNormIntegrals

namespace DedekindZetaZeroFree

open KPContSectorCoveredQuotientVocabulary KPContSectorScalarLineAlgebra
open KPContSectorSmoothFramesSupport KPContSectorFixedPushforwardSupport
open KPContSectorFiniteOrbitIntegral KPContSectorFixedLineNormIntegrals
open KPContSectorQuotientRelationsComparison
open KPMsFixedHaarDisintegration

private theorem fixedLine_sigma_integral {ι : Type*} [Fintype ι]
    {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, MeasurableSpace (X i)]
    [∀ i, OpensMeasurableSpace (X i)]
    {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (e : (Σ i, X i) ≃ₜ Y) (μ : Measure Y) (w : ι → ℝ≥0∞) (ν : ∀ i, Measure (X i))
    (hm : ∀ i, μ.restrict (Set.range (fun x : X i => e ⟨i,x⟩)) =
      w i • Measure.map (fun x : X i => e ⟨i,x⟩) (ν i))
    (g : Y → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ y, g y ∂μ) = ∑ i, w i * ∫⁻ x, g (e ⟨i,x⟩) ∂ν i := by
  classical
  let s : ι → Set Y := fun i => Set.range (fun x : X i => e ⟨i,x⟩)
  have hs : ∀ i, MeasurableSet (s i) := by
    intro i
    have heq : s i = e '' Set.range (@Sigma.mk ι X i) := by
      exact Set.range_comp ..
    rw [heq]
    exact (e.isOpenMap _ isOpen_range_sigmaMk).measurableSet
  have hd : Pairwise (fun i j => Disjoint (s i) (s j)) := by
    intro i j hij
    refine Set.disjoint_left.mpr ?_
    rintro y ⟨x, rfl⟩ ⟨z, he⟩
    have h := congrArg Sigma.fst (e.injective he)
    exact hij h.symm
  have hu : (⋃ i, s i) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    obtain ⟨⟨i,x⟩, rfl⟩ := e.surjective y
    exact Set.mem_iUnion.mpr ⟨i, x, rfl⟩
  have hμ : μ = Measure.sum (fun i => μ.restrict (s i)) := by
    rw [← Measure.restrict_iUnion hd hs, hu, Measure.restrict_univ]
  rw [hμ, lintegral_sum_measure, tsum_fintype]
  apply Finset.sum_congr rfl
  intro i hi
  have hmi : Measurable (fun x : X i => e ⟨i,x⟩) :=
    (e.continuous.comp continuous_sigmaMk).measurable
  rw [hm i, lintegral_smul_measure, lintegral_map hg hmi]
  rfl

theorem kp_cont_sector_fixed_line_norm_integrals
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (f : KPContSectorScalarLineAlgebra.GenuineCoveredScalars F ζ hζ U)
    (hf : Measurable f.val) :
    KPContSectorFixedLineNormIntegrals.NormIdentities F ζ hζ U R P H f := by
  classical
  letI : Fintype (rootsOfUnity 3 F) := Fintype.ofFinite _
  let ψ : CoveredSpherical F ζ hζ U → ℝ≥0∞ :=
    fun v => ENNReal.ofReal (‖f.val v‖ ^ 2)
  have hψ : Measurable ψ :=
    ENNReal.measurable_ofReal.comp (hf.norm.pow_const 2)
  have hqm := (q_continuous F ζ hζ U).measurable
  have hpull : ∀ v : CoveredSpherical F ζ hζ U,
      lineNorm F ζ hζ U R P H f (q F ζ hζ U v) = ENNReal.ofReal (‖f.val v‖ ^ 2) := by
    intro v
    simp only [lineNorm, sectionNorm_pullback F ζ hζ U R P H f v]
  have havg (v : CoveredSpherical F ζ hζ U) : centralAverage F ζ hζ U ψ v = ψ v := by
    have hterm (ε : rootsOfUnity 3 F) : ψ (z F ζ hζ U ε v) = ψ v := by
      dsimp [ψ]
      rw [f.property ε v, norm_mul, chi_coe F ζ hζ ε, chi_norm F ζ hζ ε, one_mul]
    simp_rw [centralAverage, hterm, Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card, card_cubic_center F ζ hζ]
    simp [← mul_assoc, ENNReal.inv_mul_cancel (by norm_num : (3 : ℝ≥0∞) ≠ 0)
      (by norm_num : (3 : ℝ≥0∞) ≠ ∞)]
  have hdesc : borelDescent F ζ hζ U ψ hψ = lineNorm F ζ hζ U R P H f := by
    funext b
    obtain ⟨v, rfl⟩ := q_surjective F ζ hζ U b
    rw [borelDescent_q F ζ hζ U ψ hψ v, havg v, hpull v]
  have hcpl : ∀ (i : Fin (H.atlas U).componentCount)
      (x : KPCuspSiegel.OrbitQuotient F
        (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i))),
      lineNorm F ζ hζ U R P H f
        (KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative i) x) =
        componentLineNorm F ζ hζ U R P H f i x := by
    intro i x
    refine Quotient.inductionOn x ?_
    intro y
    simp only [lineNorm, componentLineNorm, sectionNorm]
    rw [← (H.atlas U).components_formula i (Quotient.mk _ y)]
    rw [show (H.atlas U).components.symm ((H.atlas U).components ⟨i, Quotient.mk _ y⟩) =
        ⟨i, Quotient.mk _ y⟩ from Equiv.symm_apply_apply _ _]
  have hdecomp (g : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ≥0∞) (hg : Measurable g)
      (E : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)) (hE : MeasurableSet E) :
      (∫⁻ b in E, g b ∂sphericalMeasure F ζ hζ R P U) =
      ∑ i : Fin (H.atlas U).componentCount, (H.disintegration U).componentWeight i *
        ∫⁻ x in (KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative i)) ⁻¹' E,
          g (KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative i) x)
          ∂KPFiniteCuspAtlas.quotientVolume F
            (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i))
            ((H.atlas U).cuspAtlas i).fundamentalDomain := by
    rw [← lintegral_indicator hE]
    letI : ∀ i : Fin (H.atlas U).componentCount,
        OpensMeasurableSpace (KPCuspSiegel.OrbitQuotient F
          (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i))) :=
      fun i => ⟨MeasurableSpace.generateFrom_le (fun s hs =>
        measurableSet_quotient.mpr
          ((show IsOpen s from hs).preimage continuous_quotient_mk').measurableSet)⟩
    have hmaps : ∀ i, KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative i) =
        fun x => (H.atlas U).components ⟨i,x⟩ := by
      intro i; funext x; exact ((H.atlas U).components_formula i x).symm
    have hm := fun i => (H.disintegration U).component_measure i
    simp only [hmaps] at hm ⊢
    rw [fixedLine_sigma_integral (H.atlas U).components _ _ _ hm _ (hg.indicator hE)]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    have hmi : Measurable (fun x => (H.atlas U).components ⟨i,x⟩) :=
      ((H.atlas U).components.continuous.comp continuous_sigmaMk).measurable
    rw [← lintegral_indicator (hE.preimage hmi)]
    apply lintegral_congr
    intro x
    by_cases hx : (H.atlas U).components ⟨i,x⟩ ∈ E <;> simp [hx]
  have hln : Measurable (lineNorm F ζ hζ U R P H f) := by
    rw [← hdesc]; exact borelDescent_measurable F ζ hζ U ψ hψ
  refine ⟨hln, fun i x => ?_, fun i => ?_, fun E hE => ?_, fun E hE => ?_, fun hf2 => ?_⟩
  · simp only [lineNorm, sectionNorm_component F ζ hζ U R P H (S F ζ hζ U R P H f) i x]
  · convert hln.comp ((H.atlas U).components.continuous.comp continuous_sigmaMk).measurable using 1
    funext x
    exact (hcpl i x).symm.trans (congrArg _ ((H.atlas U).components_formula i x).symm)
  · have hmeas : MeasurableSet ((q F ζ hζ U) ⁻¹' E) := hE.preimage hqm
    rw [← lintegral_indicator hmeas ψ, ← lintegral_indicator hE (lineNorm F ζ hζ U R P H f)]
    rw [← hdesc]
    exact lintegral_indicator_borelDescent F ζ hζ R P U ψ hψ E hE
  · rw [hdecomp _ hln E hE]
    apply Finset.sum_congr rfl
    intro i hi
    simp_rw [hcpl i]
  · rw [Lp.norm_toLp f.val hf2,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
        hf2.aestronglyMeasurable]
    have hlm : Measurable (lineNorm F ζ hζ U R P H f) := by
      rw [← hdesc]; exact borelDescent_measurable F ζ hζ U ψ hψ
    have hkey : (∫⁻ v, ψ v ∂coveredMeasure F ζ hζ R U) =
        ∫⁻ b, lineNorm F ζ hζ U R P H f b
          ∂KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U := by
      rw [← map_q_coveredMeasure F ζ hζ R P U, lintegral_map hlm hqm]
      apply lintegral_congr
      intro v
      exact (hpull v).symm
    have hinner : (∫⁻ v, ‖f.val v‖ₑ ^ (ENNReal.toReal 2)
          ∂coveredMeasure F ζ hζ R U) =
        ∫⁻ v, ψ v ∂coveredMeasure F ζ hζ R U := by
      apply lintegral_congr
      intro v
      rw [show ‖f.val v‖ₑ = ENNReal.ofReal ‖f.val v‖ by simp, ENNReal.toReal_ofNat,
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (f.val v)) (by norm_num),
        show (‖f.val v‖ : ℝ) ^ (2 : ℝ) = ‖f.val v‖ ^ 2 from Real.rpow_two _]
    rw [hinner, hkey]
    simp only [ENNReal.toReal_ofNat]
    rw [← ENNReal.toReal_rpow, ← Real.sqrt_eq_rpow, Real.sq_sqrt ENNReal.toReal_nonneg]

end DedekindZetaZeroFree

end
