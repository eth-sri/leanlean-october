module

public import DedekindZetaZeroFree.Adeles.Quotients.PGLContinuity

public import DedekindZetaZeroFree.Theta.Unfolding.TraceNormalizedSourceData
public import DedekindZetaZeroFree.Eisenstein.ConstantTerms.CompactPeriod.QuotientDescent
public import DedekindZetaZeroFree.Adeles.Characters.FiniteOrderLocalRegularity

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory IsDedekindDomain
namespace DedekindZetaZeroFree.DigitMasks
open MomentSources ThetaProfileHaarSheets ThetaSheetExactUnfolding
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

attribute [local instance] KPAdelicCoverRestrictedProduct.localTopology
  KPAdelicCoverRestrictedProduct.pglLocalTopology

 theorem localIdele_continuous (v : KPHilbert.Place F) :
    Continuous (KPRationalAdelicSplitting.localIdele F v) := by
  cases v with
  | inl w =>
    change Continuous (Units.map (NumberField.AdeleRing.ofCompletion (𝓞 F) F w))
    apply Continuous.units_map
    change Continuous (fun z : w.Completion =>
      (NumberField.InfiniteAdeleRing.ofCompletion w z, (1 : FiniteAdeleRing (𝓞 F) F)))
    apply Continuous.prodMk _ continuous_const
    change Continuous (fun z : w.Completion => Pi.mulSingle w z)
    fun_prop
  | inr q =>
    change Continuous (Units.map (NumberField.AdeleRing.ofAdicCompletion (𝓞 F) F q))
    apply Continuous.units_map
    change Continuous (fun z : q.adicCompletion F =>
      ((1 : InfiniteAdeleRing F), FiniteAdeleRing.ofAdicCompletion F q z))
    apply Continuous.prodMk continuous_const
    let a := fun w : IsDedekindDomain.HeightOneSpectrum (𝓞 F) =>
      (w.adicCompletionIntegers F : Set (w.adicCompletion F))
    let f : q.adicCompletion F → RestrictedProduct
        (fun w : IsDedekindDomain.HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
        a (Filter.principal {q}ᶜ) := fun z => ⟨Pi.mulSingle q z, by
      rw [Filter.eventually_principal]
      intro w hw
      rw [Pi.mulSingle_eq_of_ne (by simpa using hw)]
      exact one_mem _⟩
    have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.mpr (by
      change Continuous (fun z : q.adicCompletion F => Pi.mulSingle q z)
      fun_prop)
    have hi : Filter.cofinite ≤ Filter.principal
        ({q}ᶜ : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) := by simp
    exact (RestrictedProduct.continuous_inclusion hi).comp hf

 theorem localIdele_selected_continuous (R : PrincipalMellin.ActualRecipe S η) :
    Continuous (localIdele R) := by
  unfold localIdele
  apply Continuous.mul
  · apply continuous_finset_prod
    intro w _
    exact (localIdele_continuous (Sum.inl w)).comp ((continuous_apply w).comp continuous_fst)
  · apply continuous_finset_prod
    intro p _
    exact (localIdele_continuous (Sum.inr p.val)).comp ((continuous_apply p).comp continuous_snd)

open KPAdelicCoverRestrictedProduct

theorem diagonal_selected_continuous (R : PrincipalMellin.ActualRecipe S η) :
    Continuous (diagonal R) :=
  (OrbitExpansion.pglA_continuous R.A).comp (localIdele_selected_continuous R)

theorem signedArgument_continuous (R : PrincipalMellin.ActualRecipe S η)
    (m : ThetaReflectionData.Row R.A) (b : Bool)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property)) :
    Continuous (fun y => signedArgument R m b y d) := by
  letI : IsTopologicalGroup (Group R) :=
    (adelic_pgl_topological_cover F R.A.zeta12 R.A.primitive_zeta12).2.2.1
  exact (continuous_const.mul (diagonal_selected_continuous R)).mul continuous_const

theorem signedDigits_continuous (R : PrincipalMellin.ActualRecipe S η)
    {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (b : Bool) :
    Continuous (signedDigits R Q T v m b) := by
  apply continuous_finset_sum
  intro d _
  exact continuous_const.mul ((T.automorphic v).1.1.comp (signedArgument_continuous R m b d))

 instance groupSecondCountable (A : SArithmeticData F) : SecondCountableTopology A.G := by
  letI : ∀ w : InfinitePlace F, SecondCountableTopology w.Completion := fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (A.complex_place w)).toHomeomorph.secondCountableTopology
  letI : ∀ w : InfinitePlace F, SecondCountableTopology w.Completionˣ := fun w =>
    Units.isEmbedding_val₀.secondCountableTopology
  infer_instance

private theorem sixthPowers_measurable (A : SArithmeticData F) :
    MeasurableSet (A.sixthPowers : Set A.G) := by
  have h : IsSigmaCompact (Set.range (fun y : A.G => y ^ 6)) :=
    isSigmaCompact_range (continuous_id.pow 6)
  obtain ⟨K, hK, hU⟩ := h
  change MeasurableSet (Set.range (fun y : A.G => y ^ 6))
  rw [← hU]
  exact MeasurableSet.iUnion (fun i => (hK i).measurableSet)

private theorem class_measurableSingleton (A : SArithmeticData F) :
    MeasurableSingletonClass A.V := by
  constructor
  intro q
  obtain ⟨y, rfl⟩ := (QuotientGroup.mk'_surjective A.sixthPowers) q
  apply measurableSet_quotient.mpr
  have he : (Quotient.mk'' ⁻¹' {QuotientGroup.mk' A.sixthPowers y} : Set A.G) =
      (fun z => z / y) ⁻¹' (A.sixthPowers : Set A.G) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact QuotientGroup.eq_iff_div_mem
  rw [he]
  exact (sixthPowers_measurable A).preimage
    ((continuous_id : Continuous (fun z : A.G => z)).div' continuous_const).measurable

theorem finite_class_measurable (A : SArithmeticData F) (f : A.V → ℂ) :
    Measurable (fun y => f (QuotientGroup.mk' A.sixthPowers y)) := by
  letI := class_measurableSingleton A
  letI := A.V_finite
  exact (measurable_of_finite f).comp
    (measurable_quotient_mk'' (s := QuotientGroup.leftRel A.sixthPowers))

private theorem correctionLS_continuous (A : SArithmeticData F)
    {σ : F →+* ℂ} {η : RayClassCharacter F A.modulus}
    {hS : A.ContainsTraceBadPlaces} (D : A.GaussCorrectionOutput σ η hS) :
    Continuous (A.correctionLS D.Λ D.G D.η_id) := by
  unfold SArithmeticData.correctionLS SArithmeticData.ideleSInverseProduct
  have hθ := SArithmeticData.CorrectionAssembly.correctionTheta_continuous A
    D.Λ D.G D.η_id D.Λ_continuous D.G_continuous D.eta_continuous
  apply Continuous.mul
  · apply continuous_finset_prod
    intro w _
    exact (hθ.comp ((SArithmeticData.CorrectionTopology.infinite_embedding_continuous w).comp
      ((continuous_apply w).comp continuous_fst))).inv
  · apply continuous_finset_prod
    intro p _
    exact (hθ.comp ((SArithmeticData.CorrectionTopology.finite_embedding_continuous p.val).comp
      ((continuous_apply p).comp continuous_snd))).inv

theorem branch_measurable (R : PrincipalMellin.ActualRecipe S η)
    {Q : AdmissibleFlatSources R} (P : Packet R Q) (v : R.A.UnitQuotient) :
    Measurable (P.branch v) := by
  have hH := finite_class_measurable R.A (fun q =>
    R.σ ((R.A.H_S6 (QuotientGroup.mk' R.A.sixthPowers
      (R.A.diagonal (R.probe.unitReps.representative v).val)) q : Fˣ) : F))
  have hLS : Measurable (fun y : R.A.G =>
      (R.A.correctionLS R.probe.correction.Λ R.probe.correction.G R.probe.correction.η_id y : ℂ)) :=
    (continuous_subtype_val.comp (correctionLS_continuous R.A R.probe.correction)).measurable
  convert hLS.mul hH using 1
  funext y
  simp only [Pi.mul_apply]
  rw [P.branch_global, R.A.H_S6_on_representatives]

theorem root_norm (R : PrincipalMellin.ActualRecipe S η) (h : rootsOfUnity 6 F) :
    ‖R.σ ((h : Fˣ) : F)‖ = 1 := by
  apply Complex.norm_eq_one_of_pow_eq_one (n := 6) _ (by norm_num)
  rw [← map_pow, ← Units.val_pow_eq_pow_val]
  have hh : (h : Fˣ) ^ 6 = 1 := (mem_rootsOfUnity _ _).mp h.property
  rw [hh]
  simp

theorem branch_norm (R : PrincipalMellin.ActualRecipe S η)
    {Q : AdmissibleFlatSources R} (P : Packet R Q) (v : R.A.UnitQuotient) (y : R.A.G) :
    ‖P.branch v y‖ = 1 := by
  rw [P.branch_global, norm_mul, Circle.norm_coe, root_norm, one_mul]

def thetaWeight (R : PrincipalMellin.ActualRecipe S η)
    {Q : AdmissibleFlatSources R} (P : Packet R Q) (v : R.A.UnitQuotient) (y : R.A.G) : ℂ :=
  (if QuotientGroup.mk' R.A.sixthPowers y ∈ R.probe.correction.B then 1 else 0) *
    (P.branch v y)⁻¹

theorem thetaWeight_measurable (R : PrincipalMellin.ActualRecipe S η)
    {Q : AdmissibleFlatSources R} (P : Packet R Q) (v : R.A.UnitQuotient) :
    Measurable (thetaWeight R P v) :=
  (finite_class_measurable R.A (fun q => if q ∈ R.probe.correction.B then 1 else 0)).mul
    (branch_measurable R P v).inv

theorem thetaWeight_norm_le_one (R : PrincipalMellin.ActualRecipe S η)
    {Q : AdmissibleFlatSources R} (P : Packet R Q) (v : R.A.UnitQuotient) (y : R.A.G) :
    ‖thetaWeight R P v y‖ ≤ 1 := by
  unfold thetaWeight
  rw [norm_mul, norm_inv, branch_norm, inv_one, mul_one]
  split_ifs <;> norm_num

 instance sheetFiniteOnCompacts (A : SArithmeticData F) (v₀ : InfinitePlace F)
    (μG : Measure A.G) [μG.IsHaarMeasure] (l : PositiveAxis) :
    IsFiniteMeasureOnCompacts (sheetHaar A v₀ μG l) where
  lt_top_of_isCompact := by
    intro J hJ
    unfold sheetHaar
    rw [Measure.map_apply (sheetTranslation A v₀ l).measurable hJ.measurableSet]
    apply IsCompact.measure_lt_top
    convert hJ.image (sheetTranslation A v₀ l).symm.continuous using 1
    exact ((sheetTranslation A v₀ l).toEquiv.image_symm_eq_preimage J).symm

theorem quotient_integrable_of_continuous_bdd_weight
    (A : SArithmeticData F) (v₀ : InfinitePlace F)
    (μG : Measure A.G) [μG.IsHaarMeasure] (l : PositiveAxis)
    (f weight : A.G → ℂ) (qf : SheetQuotient A l → ℂ)
    (hf : Continuous f) (hw : Measurable weight)
    (hbound : ∀ y, ‖weight y‖ ≤ 1)
    (hdesc : ∀ y : Sheet A l, qf (sheetProjection A l y) = weight y.val * f y.val) :
    Integrable qf (sheetQuotientHaar A v₀ μG l) := by
  obtain ⟨Ω, _, hΩc, _, hΩ⟩ := exists_sheetFundamentalDomain A v₀ μG l
  have hcomp : qf ∘ sheetProjection A l =
      fun y : Sheet A l => weight y.val * f y.val := funext hdesc
  have hmeas : Measurable qf := by
    apply measurable_from_quotient.mpr
    change Measurable (qf ∘ sheetProjection A l)
    rw [hcomp]
    exact (hw.comp measurable_subtype_coe).mul
      (hf.comp continuous_subtype_val).measurable
  apply ((sheetProjection_measurePreserving A v₀ μG l Ω hΩ).integrable_comp
    hmeas.stronglyMeasurable.aestronglyMeasurable).mp
  rw [hcomp]
  have hi : IntegrableOn (fun y : Sheet A l => f y.val) Ω (sheetHaar A v₀ μG l) :=
    ((hf.comp continuous_subtype_val).continuousOn.integrableOn_compact hΩc).mono_set
      subset_closure
  exact hi.bdd_mul (hw.comp measurable_subtype_coe).stronglyMeasurable.aestronglyMeasurable
    (c := 1) (Filter.Eventually.of_forall fun y => hbound y.val)

theorem quotientTheta_projection (R : PrincipalMellin.ActualRecipe S η)
    {Q : AdmissibleFlatSources R} (T : Realization R Q) (P : Packet R Q)
    (hdesc : ∀ v m b (γ : R.A.Gamma) y,
      weightedDigits R Q T P v m b (γ.val * y) = weightedDigits R Q T P v m b y)
    (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (b : Bool)
    (l : PositiveAxis) (y : Sheet R.A l) :
    quotientTheta R Q T P v m b l (sheetProjection R.A l y) =
      thetaWeight R P v y.val * signedDigits R Q T v m b y.val := by
  let y' : Sheet R.A l := Quotient.out (sheetProjection R.A l y)
  have hrel : MulAction.orbitRel R.A.Gamma1 (Sheet R.A l) y' y :=
    Quotient.exact (Quotient.out_eq (sheetProjection R.A l y))
  obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hrel)
  have hv : y'.val = γ.val.val * y.val := (congrArg Subtype.val hγ).symm
  change weightedDigits R Q T P v m b y'.val = _
  rw [hv, hdesc v m b ⟨γ.val.val, γ.property⟩ y.val]
  rfl

end DedekindZetaZeroFree.DigitMasks

end
