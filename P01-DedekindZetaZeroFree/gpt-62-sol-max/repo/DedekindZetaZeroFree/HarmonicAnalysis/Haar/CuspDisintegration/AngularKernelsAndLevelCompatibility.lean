module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspRadialIntegrationAndShellVolumes
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.AdelicComponents.ProductDisintegration
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.ArithmeticComponents.HyperbolicQuotientVolume
public import DedekindZetaZeroFree.Geometry.Cusps.FundamentalDomains.ExactRectangles
public import DedekindZetaZeroFree.Geometry.Cusps.AffineTorusBundles.RadialProductPresentation

@[expose] public section

noncomputable section
open scoped Classical NumberField
namespace DedekindZetaZeroFree.KPMsFixedHaar

section AngularMarginal
open MeasureTheory
open scoped ENNReal
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {hF : NumberField.InfinitePlace.nrRealPlaces F = 0} {U : Level F ζ hζ}
variable (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)

 theorem angular_measurable : Measurable (angularProjection A) := by
  apply Continuous.measurable
  apply continuous_sigma
  intro j
  exact continuous_sigmaMk.comp (Geometry A j).atlas.continuous_projection

private theorem kernel_angular_map (K : FiberKernel A) (ω : Omega A) :
    Measure.map (angularProjection A) (K.unipotent ω) = Measure.dirac ω := by
  rcases ω with ⟨j, b⟩
  induction b using QuotientAddGroup.induction_on with
  | H b =>
    obtain ⟨dn, hdn, hprob, hformula⟩ := K.fiber_formula j b
    letI := hprob
    haveI : DiscreteTopology (KPCuspCharts.translationLattice F (Parabolic A j).L) :=
      (Geometry A j).lattice.choose
    haveI : IsClosed (KPCuspCharts.translationLattice F (Parabolic A j).L :
        Set (KPCuspCharts.Horizontal F)) := AddSubgroup.isClosed_of_discreteTopology
    let lift := fun z : KPCuspCharts.Torus F (Parabolic A j).L =>
      (⟨j, (Geometry A j).atlas.lift (z,b)⟩ : CrossSection A)
    have hlift : Measurable lift := by
      apply Continuous.measurable
      exact continuous_sigmaMk.comp ((Geometry A j).atlas.continuous_lift.comp
        (continuous_id.prodMk continuous_const))
    have hconstant : angularProjection A ∘ lift = fun _ =>
        (⟨j, QuotientAddGroup.mk b⟩ : Omega A) := by
      funext z
      induction z using QuotientAddGroup.induction_on with
      | H x =>
        dsimp [lift, angularProjection]
        rw [(Geometry A j).atlas.lift_formula, (Geometry A j).atlas.projection_formula]
    rw [hformula, Measure.map_map (angular_measurable A) hlift, hconstant,
      Measure.map_const, measure_univ, one_smul]

 theorem kernel_angular_lintegral (K : FiberKernel A) (ω : Omega A)
    (f : Omega A → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f (angularProjection A x) ∂K.unipotent ω) = f ω := by
  rw [← lintegral_map hf (angular_measurable A), kernel_angular_map A K ω,
    lintegral_dirac' _ hf]

 theorem cross_section_inclusion_measurable (j : CuspIndex A) :
    Measurable (fun x => (⟨j,x⟩ : CrossSection A)) := by
  apply measurable_from_quotient.mpr
  have hmk : Continuous (fun p : KPCuspCharts.Cross F =>
      (⟨j, Quotient.mk _ p⟩ : CrossSection A)) :=
    continuous_sigmaMk.comp continuous_quotient_mk'
  exact hmk.measurable

 def weighted_section_measure (w : Fin A.componentCount → ℝ≥0∞) :
    Measure (CrossSection A) :=
  ∑ j : CuspIndex A,
    (w j.1 / ENNReal.ofReal (2 * (KPCuspLogShape.dimension F : ℝ))) •
      Measure.map (fun x => (⟨j, x⟩ : CrossSection A)) (Geometry A j).sectionMeasure

 theorem angular_marginal_of_disintegration (K : FiberKernel A)
    (w : Fin A.componentCount → ℝ≥0∞) (β : Measure (Omega A))
    (h : ∀ f : CrossSection A → ℝ≥0∞, Measurable f →
      (∑ j : CuspIndex A,
        (w j.1 / ENNReal.ofReal (2 * (KPCuspLogShape.dimension F : ℝ))) *
          ∫⁻ x, f ⟨j,x⟩ ∂(Geometry A j).sectionMeasure) =
        ∫⁻ ω, ∫⁻ x, f x ∂K.unipotent ω ∂β) :
    Measure.map (angularProjection A) (weighted_section_measure A w) = β := by
  apply Measure.ext
  intro E hE
  let f : Omega A → ℝ≥0∞ := E.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hE
  have hid := h (fun x => f (angularProjection A x)) (hf.comp (angular_measurable A))
  simp_rw [kernel_angular_lintegral A K _ f hf] at hid
  have he : (∫⁻ x, f (angularProjection A x) ∂weighted_section_measure A w) =
      ∑ j : CuspIndex A,
        (w j.1 / ENNReal.ofReal (2 * (KPCuspLogShape.dimension F : ℝ))) *
          ∫⁻ x, f (angularProjection A ⟨j,x⟩) ∂(Geometry A j).sectionMeasure := by
    simp only [weighted_section_measure, lintegral_finsetSum_measure, lintegral_smul_measure]
    apply Finset.sum_congr rfl
    intro j _
    have hm := cross_section_inclusion_measurable A j
    have hmf : Measurable (fun x => f (angularProjection A x)) :=
      hf.comp (angular_measurable A)
    rw [lintegral_map hmf hm]
    rfl
  calc
    _ = ∫⁻ x, f x ∂Measure.map (angularProjection A) (weighted_section_measure A w) :=
      (lintegral_indicator_one hE).symm
    _ = ∫⁻ x, f (angularProjection A x) ∂weighted_section_measure A w :=
      lintegral_map hf (angular_measurable A)
    _ = ∫⁻ ω, f ω ∂β := he.trans hid
    _ = β E := lintegral_indicator_one hE

 def weighted_angular_measure (w : Fin A.componentCount → ℝ≥0∞) :
    Measure (Omega A) :=
  Measure.map (angularProjection A) (weighted_section_measure A w)

private theorem weighted_section_mass (w : Fin A.componentCount → ℝ≥0∞) :
    weighted_section_measure A w Set.univ =
      ∑ j : CuspIndex A,
        (w j.1 / ENNReal.ofReal (2 * (KPCuspLogShape.dimension F : ℝ))) *
          (Geometry A j).sectionMeasure Set.univ := by
  simp only [weighted_section_measure, Measure.finsetSum_apply, Measure.smul_apply,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [Measure.map_apply (cross_section_inclusion_measurable A j) MeasurableSet.univ,
    Set.preimage_univ]

private theorem weighted_angular_apply (w : Fin A.componentCount → ℝ≥0∞)
    (E : Set (Omega A)) (hE : MeasurableSet E) :
    weighted_angular_measure A w E =
      ∑ j : CuspIndex A,
        (w j.1 / ENNReal.ofReal (2 * (KPCuspLogShape.dimension F : ℝ))) *
          (Geometry A j).sectionMeasure
            ((fun x => (⟨j, (Geometry A j).atlas.projection x⟩ : Omega A)) ⁻¹' E) := by
  rw [weighted_angular_measure, Measure.map_apply (angular_measurable A) hE]
  simp only [weighted_section_measure, Measure.finsetSum_apply, Measure.smul_apply,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [Measure.map_apply (cross_section_inclusion_measurable A j)
    ((angular_measurable A) hE)]
  rfl

 theorem weighted_section_finite (w : Fin A.componentCount → ℝ≥0∞)
    (hw : ∀ i, w i < ⊤) : IsFiniteMeasure (weighted_section_measure A w) := by
  constructor
  rw [weighted_section_mass A w]
  apply ENNReal.sum_lt_top.mpr
  intro j _
  apply ENNReal.mul_lt_top
  · apply ENNReal.div_lt_top (ne_of_lt (hw j.1))
    apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    exact mul_pos (by norm_num) (Nat.cast_pos.mpr (KPCuspLogShape.dimension_pos F hF))
  · exact (Geometry A j).finite_sectionMeasure.measure_univ_lt_top

private theorem weighted_section_positive (w : Fin A.componentCount → ℝ≥0∞)
    (hw : ∀ i, 0 < w i) : weighted_section_measure A w Set.univ ≠ 0 := by
  apply ne_of_gt
  rw [weighted_section_mass A w]
  apply Finset.sum_pos_iff.mpr
  let i : Fin A.componentCount := ⟨0, A.positive_componentCount⟩
  let a : Fin (A.cuspAtlas i).cuspCount := ⟨0, (A.cuspAtlas i).positive_cuspCount⟩
  refine ⟨⟨i,a⟩, Finset.mem_univ _, ?_⟩
  apply ENNReal.mul_pos
  · exact ENNReal.div_ne_zero.mpr ⟨ne_of_gt (hw i), ENNReal.ofReal_ne_top⟩
  · exact (Geometry A ⟨i,a⟩).positive_sectionMeasure

private theorem weighted_angular_finite (w : Fin A.componentCount → ℝ≥0∞)
    (hw : ∀ i, w i < ⊤) : IsFiniteMeasure (weighted_angular_measure A w) := by
  letI := weighted_section_finite A w hw
  unfold weighted_angular_measure
  infer_instance

private theorem weighted_angular_positive (w : Fin A.componentCount → ℝ≥0∞)
    (hw : ∀ i, 0 < w i) : weighted_angular_measure A w Set.univ ≠ 0 := by
  rw [weighted_angular_measure, Measure.map_apply (angular_measurable A) MeasurableSet.univ,
    Set.preimage_univ]
  exact weighted_section_positive A w hw

private theorem weighted_angular_probability (w : Fin A.componentCount → ℝ≥0∞)
    (hpos : ∀ i, 0 < w i) (hfin : ∀ i, w i < ⊤) :
    IsProbabilityMeasure (probability A (weighted_angular_measure A w)) := by
  constructor
  simp only [probability, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (weighted_angular_positive A w hpos)
    (weighted_angular_finite A w hfin).measure_univ_lt_top.ne

end AngularMarginal

 theorem probability_map
    {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0} {V U : Level F ζ hζ}
    (AV : KPFiniteCuspAtlas.Atlas F ζ hζ hF V)
    (AU : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (βV : MeasureTheory.Measure (Omega AV)) (βU : MeasureTheory.Measure (Omega AU))
    (f : Omega AV → Omega AU) (hf : Measurable f)
    (hβ : MeasureTheory.Measure.map f βV = βU) :
    MeasureTheory.Measure.map f (probability AV βV) = probability AU βU := by
  have hmass : βV Set.univ = βU Set.univ := by
    rw [← hβ, MeasureTheory.Measure.map_apply hf MeasurableSet.univ, Set.preimage_univ]
  simp only [probability]
  rw [MeasureTheory.Measure.map_smul _ hf.aemeasurable, hmass, hβ]

section FiniteIsotropyMeasureComparison
open MeasureTheory Set
open scoped ENNReal Pointwise

private theorem lintegral_constant_orbit_multiplicity
    {H X : Type*} [Group H] [Countable H] [MeasurableSpace X]
    [MulAction H X] [MeasurableConstSMul H X]
    (ν : Measure X) [SMulInvariantMeasure H X ν]
    {s t : Set X} (hs : IsFundamentalDomain H s ν)
    (ht : MeasurableSet t) (c : ℝ≥0∞)
    (hcount : ∀ᵐ x ∂ν.restrict s,
      (∑' g : H, (g • t).indicator (fun _ => (1 : ℝ≥0∞)) x) = c)
    (f : X → ℝ≥0∞) (hinv : ∀ (g : H) (x : X), f (g • x) = f x) :
    (∫⁻ x in t, f x ∂ν) = c * ∫⁻ x in s, f x ∂ν := by
  have hm : (Measure.sum fun g : H => ν.restrict (g • t ∩ s)) =
      c • ν.restrict s :=
    KPMeanZeroWeightedEnergy.GapCoercivity.CrossSection.OrbitMultiplicity.sum_restrict_of_constant_multiplicity
      ν s (fun g : H => g • t) (fun g => ht.const_smul g) c hcount
  calc
    (∫⁻ x in t, f x ∂ν) = ∑' g : H, ∫⁻ x in g • t ∩ s, f x ∂ν := by
      rw [hs.setLIntegral_eq_tsum']
      simp only [hinv]
    _ = ∫⁻ x, f x ∂(Measure.sum fun g : H => ν.restrict (g • t ∩ s)) := by
      rw [lintegral_sum_measure]
    _ = c * ∫⁻ x in s, f x ∂ν := by rw [hm, lintegral_smul_measure, smul_eq_mul]

private theorem rectangle_section_measure
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D)
    (A : Set (KPCuspCharts.Horizontal F)) (B : Set (KPCuspCharts.Shape F))
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hA : ∀ y : KPCuspCharts.Horizontal F, ∃! l : D.L,
      y + KPCuspCharts.embedding F l.val ∈ A)
    (hB : ∀ b : KPCuspCharts.Shape F, ∃! v : KPCuspLogShape.logLattice F hF D.E D.integralUnits,
      b + v.val ∈ B) :
    Measure.map (Quotient.mk (KPCuspCharts.crossRelation F S))
      ((volume.prod G.shapeMeasure).restrict (A ×ˢ B)) =
      (Nat.card (KPCuspCharts.kernelUnits F hF D.E D.integralUnits) : ℝ≥0∞) •
        G.sectionMeasure := by
  letI : Countable F := (Module.finBasis ℚ F).repr.injective.countable
  letI : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
  letI : Countable (Matrix.GeneralLinearGroup (Fin 2) F) := Units.val_injective.countable
  letI : Countable (KPCuspArithmetic.PGL2 F) := Matrix.ProjGenLinGroup.mk_surjective.countable
  letI := KPCuspCharts.homeomorphAction G.crossAction
  letI : MeasurableConstSMul S (KPCuspCharts.Cross F) :=
    ⟨fun s => (G.crossAction s).continuous.measurable⟩
  letI := G.haar_shapeMeasure
  letI := G.finite_isotropy
  letI : SMulInvariantMeasure S (KPCuspCharts.Cross F) (volume.prod G.shapeMeasure) :=
    ⟨fun s E hE => by
      have hm := congrArg (fun ν : Measure (KPCuspCharts.Cross F) => ν E) (G.measure_invariant s)
      rw [Measure.map_apply (G.crossAction s).continuous.measurable hE] at hm
      exact hm⟩
  have hmk : ∀ (s : S) (x : KPCuspCharts.Cross F),
      Quotient.mk (KPCuspCharts.crossRelation F S) (G.crossAction s x) =
        Quotient.mk (KPCuspCharts.crossRelation F S) x := by
    intro s x
    apply Quotient.sound
    change MulAction.orbitRel S _
      (KPCuspCharts.toArch F (G.crossAction s x, 0)) (KPCuspCharts.toArch F (x, 0))
    apply MulAction.orbitRel_apply.mpr
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨s, ?_⟩
    obtain ⟨M, hM, hc⟩ := D.upper s.val s.property
    change KPCuspSiegel.action F s.val (KPCuspCharts.toArch F (x, 0)) = _
    rw [G.actual_action s M hM hc, G.crossAction_formula s M hM hc]
    rfl
  have hc : (ENat.card (KPCuspCharts.kernelUnits F hF D.E D.integralUnits) : ℝ≥0∞) =
      (Nat.card (KPCuspCharts.kernelUnits F hF D.E D.integralUnits) : ℝ≥0∞) := by
    simp [ENat.card_eq_coe_natCard]
  apply Measure.ext
  intro E hE
  let f : KPCuspCharts.CrossQuotient F S → ℝ≥0∞ := E.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hE
  have heq := lintegral_constant_orbit_multiplicity (volume.prod G.shapeMeasure)
    G.isFundamentalDomain (hAm.prod hBm)
    (Nat.card (KPCuspCharts.kernelUnits F hF D.E D.integralUnits) : ℝ≥0∞)
    (Filter.Eventually.of_forall fun x =>
      (KPMeanZeroWeightedEnergy.GapCoercivity.CrossSection.rectangle_orbit_multiplicity
        G A hA B hB x).trans hc)
    (fun x => f (Quotient.mk (KPCuspCharts.crossRelation F S) x))
    (fun s x => congrArg f (hmk s x))
  rw [G.sectionMeasure_formula, Measure.smul_apply, smul_eq_mul]
  rw [← lintegral_map hf measurable_quotient_mk'',
    ← lintegral_map hf measurable_quotient_mk''] at heq
  simpa only [f, lintegral_indicator_const hE, one_mul] using heq

private theorem horizontal_domain_map
    {X : Type*} [AddCommGroup X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X] [PolishSpace X]
    {L : AddSubgroup X} [Countable L] [T2Space (X ⧸ L)]
    [SecondCountableTopology (X ⧸ L)]
    (ν : Measure X) [ν.IsAddHaarMeasure] [ν.IsAddRightInvariant] [SigmaFinite ν]
    (μ : Measure (X ⧸ L)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    {A : Set X} (hA : IsAddFundamentalDomain L.op A ν) (hAfin : ν A ≠ ⊤) :
    Measure.map QuotientAddGroup.mk (ν.restrict A) = ν A • μ := by
  let μ' : Measure (X ⧸ L) := ν A • μ
  letI : Measure.IsAddLeftInvariant μ' := inferInstanceAs (Measure.IsAddLeftInvariant (ν A • μ))
  letI : IsFiniteMeasure μ' := ⟨by simp [μ', hAfin.lt_top]⟩
  letI : HasAddFundamentalDomain L.op X ν := hA.hasAddFundamentalDomain ν
  letI : AddQuotientMeasureEqMeasurePreimage ν μ' :=
    leftInvariantIsAddQuotientMeasureEqMeasurePreimage ν (by
      rw [hA.covolume_eq_volume ν]
      simp [μ'])
  exact (measurePreserving_quotientAddGroup_mk_of_AddQuotientMeasureEqMeasurePreimage ν hA μ').map_eq

private theorem rectangle_torus_measure
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D)
    {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (q : KPCuspCharts.CrossQuotient F S → Y) (hq : Continuous q)
    (dn : Measure (KPCuspCharts.Torus F D.L)) (hdn : dn.IsAddHaarMeasure)
    (hprob : IsProbabilityMeasure dn)
    (A : Set (KPCuspCharts.Horizontal F)) (B : Set (KPCuspCharts.Shape F))
    (hAm : MeasurableSet A) (hAb : Bornology.IsBounded A)
    (hA : ∀ y : KPCuspCharts.Horizontal F, ∃! l : D.L,
      y + KPCuspCharts.embedding F l.val ∈ A) :
    Measure.map (q ∘ Quotient.mk (KPCuspCharts.crossRelation F S))
      ((volume.prod G.shapeMeasure).restrict (A ×ˢ B)) =
    (volume A) • Measure.map (q ∘ G.atlas.lift) (dn.prod (G.shapeMeasure.restrict B)) := by
  letI := hdn
  letI := hprob
  obtain ⟨hd, _⟩ := G.lattice
  letI := hd
  letI : DiscreteTopology (KPCuspCharts.translationLattice F D.L) := hd
  letI : IsClosed (KPCuspCharts.translationLattice F D.L : Set (KPCuspCharts.Horizontal F)) :=
    AddSubgroup.isClosed_of_discreteTopology
  letI : Countable (KPCuspCharts.translationLattice F D.L) :=
    countable_of_Lindelof_of_discrete
  letI := G.haar_shapeMeasure
  have hinj : Function.Injective (KPCuspCharts.embedding F) := by
    intro a c hac
    have h0 := congrFun hac ⟨0, G.positive_dimension⟩
    exact (KPCusp.complexPlace F ⟨0, G.positive_dimension⟩).embedding.injective h0
  have htiling : ∀ y : KPCuspCharts.Horizontal F,
      ∃! l : (KPCuspCharts.translationLattice F D.L).op, l +ᵥ y ∈ A := by
    intro y
    obtain ⟨a, ha, hau⟩ := hA y
    let l : KPCuspCharts.translationLattice F D.L :=
      ⟨KPCuspCharts.embedding F a.val, ⟨a.val, a.property, rfl⟩⟩
    refine ⟨⟨AddOpposite.op l.val, l.property⟩, ha, ?_⟩
    intro k hk
    obtain ⟨c, hc, hec⟩ := k.property
    have hkc : y + KPCuspCharts.embedding F c ∈ A := by
      change y + k.val.unop ∈ A at hk
      rwa [← hec] at hk
    have he := hau ⟨c, hc⟩ hkc
    apply Subtype.ext
    apply AddOpposite.unop_injective
    exact hec.symm.trans (congrArg (fun x : D.L => KPCuspCharts.embedding F x.val) he)
  have hfd : IsAddFundamentalDomain (KPCuspCharts.translationLattice F D.L).op A volume :=
    IsAddFundamentalDomain.mk' hAm.nullMeasurableSet htiling
  have hm := horizontal_domain_map volume dn hfd hAb.measure_lt_top.ne
  have hcomp : (q ∘ G.atlas.lift) ∘ Prod.map QuotientAddGroup.mk id =
      q ∘ Quotient.mk (KPCuspCharts.crossRelation F S) := by
    funext p
    exact congrArg q (G.atlas.lift_formula p.1 p.2)
  rw [← Measure.prod_restrict]
  calc
    _ = Measure.map (q ∘ G.atlas.lift) ((Measure.map QuotientAddGroup.mk (volume.restrict A)).prod
        (G.shapeMeasure.restrict B)) := by
      have hp : (Measure.map (QuotientAddGroup.mk : KPCuspCharts.Horizontal F → KPCuspCharts.Torus F D.L) (volume.restrict A)).prod
          (G.shapeMeasure.restrict B) = Measure.map (Prod.map QuotientAddGroup.mk id)
          ((volume.restrict A).prod (G.shapeMeasure.restrict B)) := by
        simpa only [Measure.map_id] using Measure.map_prod_map (volume.restrict A)
          (G.shapeMeasure.restrict B) QuotientAddGroup.continuous_mk.measurable measurable_id
      rw [hp, Measure.map_map (hq.comp G.atlas.continuous_lift).measurable
        (QuotientAddGroup.continuous_mk.measurable.prodMap measurable_id), hcomp]
    _ = _ := by
      rw [hm, Measure.prod_smul_left]
      exact Measure.map_smul (volume A) (hq.comp G.atlas.continuous_lift).measurable.aemeasurable

private theorem section_torus_representation
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D)
    {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (q : KPCuspCharts.CrossQuotient F S → Y) (hq : Continuous q) (hqm : Measurable q)
    (dn : Measure (KPCuspCharts.Torus F D.L)) (hdn : dn.IsAddHaarMeasure)
    (hprob : IsProbabilityMeasure dn) :
    ∃ B : Set (KPCuspCharts.Shape F), ∃ c : ℝ≥0∞,
      MeasurableSet B ∧ Bornology.IsBounded B ∧ c < ⊤ ∧
      Measure.map q G.sectionMeasure =
        c • Measure.map (q ∘ G.atlas.lift) (dn.prod (G.shapeMeasure.restrict B)) := by
  obtain ⟨A, B, hAm, hAb, hBm, hBb, hA, hB⟩ :=
    KPMeanZeroWeightedEnergy.GapCoercivity.CrossSection.actual_exact_comparison_rectangle G
  let m : ℝ≥0∞ := Nat.card (KPCuspCharts.kernelUnits F hF D.E D.integralUnits)
  letI := G.finite_isotropy
  have hm0 : m ≠ 0 := by
    dsimp [m]
    exact_mod_cast (Nat.card_pos (α := KPCuspCharts.kernelUnits F hF D.E D.integralUnits)).ne'
  have hmfin : m ≠ ⊤ := ENNReal.natCast_ne_top _
  have he := congrArg (Measure.map q) (rectangle_section_measure G A B hAm hBm hA hB)
  rw [Measure.map_map hqm measurable_quotient_mk'',
    Measure.map_smul _ hqm.aemeasurable] at he
  rw [rectangle_torus_measure G q hq dn hdn hprob A B hAm hAb hA] at he
  change (volume A) • Measure.map (q ∘ G.atlas.lift) (dn.prod (G.shapeMeasure.restrict B)) =
    m • Measure.map q G.sectionMeasure at he
  refine ⟨B, m⁻¹ * volume A, hBm, hBb, ?_, ?_⟩
  · exact ENNReal.mul_lt_top (ENNReal.inv_ne_top.mpr hm0).lt_top hAb.measure_lt_top
  · have he' := congrArg (fun μ : Measure Y => m⁻¹ • μ) he
    simpa only [smul_smul, ENNReal.inv_mul_cancel hm0 hmfin, one_smul] using he'.symm

section LocalSection
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {hF : NumberField.InfinitePlace.nrRealPlaces F = 0} {U : Level F ζ hζ}
variable (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)

private theorem kernel_lintegral_measurable (K : FiberKernel A)
    (f : CrossSection A → ℝ≥0∞) (hf : Measurable f) :
    Measurable (fun ω => ∫⁻ x, f x ∂K.unipotent ω) := by
  exact (Measure.measurable_lintegral hf).comp
    (Measure.measurable_of_measurable_coe K.unipotent K.measurable_kernel)

private theorem local_section_disintegration (K : FiberKernel A) (j : CuspIndex A)
    (f : CrossSection A → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f ⟨j,x⟩ ∂(Geometry A j).sectionMeasure) =
      ∫⁻ ω, ∫⁻ x, f x ∂K.unipotent ω
        ∂Measure.map (fun x => (⟨j, (Geometry A j).atlas.projection x⟩ : Omega A))
          (Geometry A j).sectionMeasure := by
  obtain ⟨dn, hdn, hprob, _⟩ := K.fiber_formula j 0
  letI := hdn
  letI := hprob
  letI := (Geometry A j).haar_shapeMeasure
  letI : DiscreteTopology (KPCuspCharts.translationLattice F (Parabolic A j).L) :=
    (Geometry A j).lattice.choose
  letI : IsClosed (KPCuspCharts.translationLattice F (Parabolic A j).L :
      Set (KPCuspCharts.Horizontal F)) := AddSubgroup.isClosed_of_discreteTopology
  obtain ⟨B, c, hBm, hBb, hc, hrep⟩ := section_torus_representation (Geometry A j)
    (fun x => (⟨j,x⟩ : CrossSection A)) continuous_sigmaMk
    (cross_section_inclusion_measurable A j) dn hdn hprob
  let lift := fun p : KPCuspCharts.Torus F (Parabolic A j).L × KPCuspCharts.Shape F =>
    (⟨j, (Geometry A j).atlas.lift p⟩ : CrossSection A)
  change Measure.map (fun x => (⟨j,x⟩ : CrossSection A)) (Geometry A j).sectionMeasure =
    c • Measure.map lift (dn.prod ((Geometry A j).shapeMeasure.restrict B)) at hrep
  have hliftc : Continuous lift :=
    (continuous_sigmaMk (σ := fun j : CuspIndex A => KPCuspCharts.CrossQuotient F
        (KPCuspArithmetic.conjugatedStabilizer F
          (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
          ((A.cuspAtlas j.1).cusp j.2) ((A.cuspAtlas j.1).representative j.2))) (i := j)).comp
      (Geometry A j).atlas.continuous_lift
  have hlift : Measurable lift := hliftc.measurable
  have hbase : angularProjection A ∘ lift =
      fun p => (⟨j, QuotientAddGroup.mk p.2⟩ : Omega A) := by
    funext p
    obtain ⟨z,b⟩ := p
    induction z using QuotientAddGroup.induction_on with
    | H z =>
      dsimp [lift, angularProjection]
      rw [(Geometry A j).atlas.lift_formula, (Geometry A j).atlas.projection_formula]
  have hformula (b : KPCuspCharts.Shape F) :
      K.unipotent ⟨j, QuotientAddGroup.mk b⟩ =
        Measure.map (fun z => lift (z,b)) dn := by
    obtain ⟨ν, hν, hpν, heν⟩ := K.fiber_formula j b
    letI := hν
    letI := hpν
    letI := (Geometry A j).compact_torus
    letI : DiscreteTopology (KPCuspCharts.translationLattice F (Parabolic A j).L) :=
      (Geometry A j).lattice.choose
    letI : IsClosed (KPCuspCharts.translationLattice F (Parabolic A j).L :
        Set (KPCuspCharts.Horizontal F)) := AddSubgroup.isClosed_of_discreteTopology
    have he : ν = dn := Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure ν dn
    simpa only [he] using heν
  have hinc := cross_section_inclusion_measurable A j
  have hang := angular_measurable A
  have hmarg : Measure.map
      (fun x => (⟨j, (Geometry A j).atlas.projection x⟩ : Omega A))
      (Geometry A j).sectionMeasure =
      c • Measure.map (angularProjection A ∘ lift)
        (dn.prod ((Geometry A j).shapeMeasure.restrict B)) := by
    have he := congrArg (Measure.map (angularProjection A)) hrep
    rw [Measure.map_map hang hinc, Measure.map_smul _ hang.aemeasurable,
      Measure.map_map hang hlift] at he
    exact he
  rw [← lintegral_map hf hinc, hrep, lintegral_smul_measure,
    lintegral_map hf hlift, lintegral_prod_symm' (fun p => f (lift p)) (hf.comp hlift),
    hmarg, lintegral_smul_measure,
    lintegral_map (kernel_lintegral_measurable A K f hf) (hang.comp hlift)]
  simp only [smul_eq_mul]
  congr 1
  rw [lintegral_prod_symm' (fun p => ∫⁻ x, f x ∂K.unipotent ((angularProjection A ∘ lift) p))
    ((kernel_lintegral_measurable A K f hf).comp (hang.comp hlift))]
  change (∫⁻ b in B, ∫⁻ z, f (lift (z,b)) ∂dn ∂(Geometry A j).shapeMeasure) =
    ∫⁻ b in B, ∫⁻ z, ∫⁻ x, f x ∂K.unipotent ((angularProjection A ∘ lift) (z,b))
      ∂dn ∂(Geometry A j).shapeMeasure
  rw [hbase]
  apply lintegral_congr
  intro b
  dsimp only
  have hlb : Measurable (fun z => lift (z,b)) := hlift.comp (measurable_id.prodMk measurable_const)
  rw [hformula, lintegral_map hf hlb]
  simp only [lintegral_const, measure_univ, mul_one]

private theorem weighted_section_disintegration (K : FiberKernel A)
    (w : Fin A.componentCount → ℝ≥0∞)
    (f : CrossSection A → ℝ≥0∞) (hf : Measurable f) :
    (∑ j : CuspIndex A,
      (w j.1 / ENNReal.ofReal (2 * (KPCuspLogShape.dimension F : ℝ))) *
        ∫⁻ x, f ⟨j,x⟩ ∂(Geometry A j).sectionMeasure) =
      ∫⁻ ω, ∫⁻ x, f x ∂K.unipotent ω ∂weighted_angular_measure A w := by
  rw [weighted_angular_measure, weighted_section_measure,
    Measure.map_finset_sum' (angular_measurable A).aemeasurable]
  simp only [lintegral_finsetSum_measure]
  apply Finset.sum_congr rfl
  intro j _
  rw [Measure.map_smul _ (angular_measurable A).aemeasurable,
    Measure.map_map (angular_measurable A) (cross_section_inclusion_measurable A j),
    lintegral_smul_measure]
  exact congrArg (fun t => (w j.1 / ENNReal.ofReal
    (2 * (KPCuspLogShape.dimension F : ℝ))) * t)
    (local_section_disintegration A K j f hf)

end LocalSection

end FiniteIsotropyMeasureComparison

namespace PinnedRadialCharts

 theorem actual_coordinate_relation
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D) (p q : KPCuspCharts.Coordinates F) :
    KPCuspCharts.totalRelation F S p q ↔
      ∃ g : S, (G.crossAction g q.1, q.2) = p := by
  change (∃ g : S, g • KPCuspCharts.toArch F q = KPCuspCharts.toArch F p) ↔ _
  have ha (g : S) (q : KPCuspCharts.Coordinates F) :
      g • KPCuspCharts.toArch F q = KPCuspCharts.toArch F (G.crossAction g q.1, q.2) := by
    obtain ⟨M, hM, hc⟩ := D.upper g.val g.property
    change KPCuspSiegel.action F g.val _ = _
    rw [G.actual_action g M hM hc, G.crossAction_formula g M hM hc]
    rfl
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, (KPCuspCharts.toArchHomeomorph F G.positive_dimension).injective
      ((ha g q).symm.trans hg)⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, (ha g q).trans (congrArg (KPCuspCharts.toArch F) hg)⟩

 def coordinate_shear
    {F : Type} [Field F] [NumberField F]
    (a : ℝ → KPCuspCharts.Shape F) (ha : Continuous a) :
    KPCuspCharts.Coordinates F ≃ₜ KPCuspCharts.Coordinates F where
  toFun p := ((p.1.1, p.1.2 + a p.2), p.2)
  invFun p := ((p.1.1, p.1.2 - a p.2), p.2)
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := (continuous_fst.fst.prodMk
    (continuous_fst.snd.add (ha.comp continuous_snd))).prodMk continuous_snd
  continuous_invFun := (continuous_fst.fst.prodMk
    (continuous_fst.snd.sub (ha.comp continuous_snd))).prodMk continuous_snd

 theorem coordinate_shear_relation
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D)
    (a : ℝ → KPCuspCharts.Shape F) (ha : Continuous a)
    (p q : KPCuspCharts.Coordinates F) :
    KPCuspCharts.totalRelation F S (coordinate_shear a ha p) (coordinate_shear a ha q) ↔
      KPCuspCharts.totalRelation F S p q := by
  rw [actual_coordinate_relation G, actual_coordinate_relation G]
  have hc (g : S) (p : KPCuspCharts.Cross F) (b : KPCuspCharts.Shape F) :
      G.crossAction g (p.1, p.2 + b) = ((G.crossAction g p).1, (G.crossAction g p).2 + b) := by
    obtain ⟨M, hM, hM0⟩ := D.upper g.val g.property
    rw [G.crossAction_formula g M hM hM0, G.crossAction_formula g M hM hM0]
    dsimp [KPCuspCharts.crossAffine, KPCuspCharts.affine]
    congr 1
    abel
  change (∃ g : S, (G.crossAction g (q.1.1, q.1.2 + a q.2), q.2) =
    coordinate_shear a ha p) ↔ _
  have he (g : S) : (G.crossAction g (q.1.1, q.1.2 + a q.2), q.2) =
      coordinate_shear a ha (G.crossAction g q.1, q.2) := by
    rw [hc]
    rfl
  simp only [he, (coordinate_shear a ha).injective.eq_iff]

 def actual_shape_translation
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D) (b : KPCuspCharts.Shape F) :
    KPCuspCharts.CrossQuotient F S ≃ₜ KPCuspCharts.CrossQuotient F S :=
  Homeomorph.Quotient.congr
    (Homeomorph.prodCongr (Homeomorph.refl _) (Homeomorph.addRight b))
    (fun p q => by
      change KPCuspCharts.totalRelation F S (p,0) (q,0) ↔
        KPCuspCharts.totalRelation F S ((p.1,p.2+b),0) ((q.1,q.2+b),0)
      exact (coordinate_shear_relation G (fun _ => b) continuous_const (p,0) (q,0)).symm)

 theorem actual_shape_translation_formula
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D) (b : KPCuspCharts.Shape F)
    (p : KPCuspCharts.Cross F) :
    actual_shape_translation G b (Quotient.mk _ p) =
      Quotient.mk _ (p.1,p.2+b) := rfl

 def sheared_high_presentation
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D)
    (a : ℝ → KPCuspCharts.Shape F) (ha : Continuous a) (T : ℝ) :
    KPCuspCharts.CrossQuotient F S × Set.Ioi T ≃ₜ KPCuspCharts.HighQuotient F S T :=
  (G.highPresentation T).trans (Homeomorph.Quotient.congr
    ((coordinate_shear a ha).subtype (fun _ => Iff.rfl))
    (fun p q => (coordinate_shear_relation G a ha p.val q.val).symm))

private theorem sheared_high_presentation_formula
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D)
    (a : ℝ → KPCuspCharts.Shape F) (ha : Continuous a) (T : ℝ)
    (p : KPCuspCharts.Cross F) (t : Set.Ioi T) :
    sheared_high_presentation G a ha T (Quotient.mk _ p, t) =
      Quotient.mk _ (⟨((p.1, p.2 + a t.val), t.val), t.property⟩ :
        {p : KPCuspCharts.Coordinates F // T < p.2}) := by
  dsimp [sheared_high_presentation]
  rw [G.highPresentation_formula]
  rfl

 theorem sectionShape_continuous
    (F : Type) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (w : NumberField.InfinitePlace F) : Continuous (sectionShape F hF w) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  have hl : Continuous (fun r : Radius => Real.log r.val) :=
    continuous_subtype_val.log (fun r => ne_of_gt r.property)
  by_cases hi : KPCusp.complexPlace F i = w
  · convert (hl.div_const 2).sub (hl.div_const
      (2 * (KPCuspLogShape.dimension F : ℝ))) using 1
    funext r
    simp [hi]
  · convert (continuous_const (y := (0 : ℝ))).sub (hl.div_const
      (2 * (KPCuspLogShape.dimension F : ℝ))) using 1
    funext r
    simp [hi]

 def radius_log_homeomorph
    (F : Type) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0) : Radius ≃ₜ ℝ where
  toFun r := logHeight (F := F) r.val
  invFun t := ⟨Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t), Real.exp_pos _⟩
  left_inv r := by
    apply Subtype.ext
    dsimp [logHeight]
    rw [mul_div_cancel₀ _ (ne_of_gt (mul_pos (by norm_num)
      (Nat.cast_pos.mpr (KPCuspLogShape.dimension_pos F hF)))), Real.exp_log r.property]
  right_inv t := by
    dsimp [logHeight]
    rw [Real.log_exp, mul_div_cancel_left₀ t (ne_of_gt (mul_pos (by norm_num)
      (Nat.cast_pos.mpr (KPCuspLogShape.dimension_pos F hF))))]
  continuous_toFun := (continuous_subtype_val.log (fun r => ne_of_gt r.property)).div_const _
  continuous_invFun := (Real.continuous_exp.comp
    (continuous_const.mul continuous_id)).subtype_mk _

 def high_radius_log_homeomorph
    (F : Type) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (Y : ℝ) (hY : 0 < Y) : Set.Ioi Y ≃ₜ Set.Ioi (logHeight (F := F) Y) where
  toFun r := ⟨logHeight (F := F) r.val, by
    change Real.log Y / (2 * (KPCuspLogShape.dimension F : ℝ)) <
      Real.log r.val / (2 * (KPCuspLogShape.dimension F : ℝ))
    apply (div_lt_div_iff_of_pos_right (mul_pos (by norm_num)
      (Nat.cast_pos.mpr (KPCuspLogShape.dimension_pos F hF)))).mpr
    exact Real.log_lt_log hY r.property⟩
  invFun t := ⟨Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t.val), by
    change Y < Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * t.val)
    calc Y = Real.exp (Real.log Y) := (Real.exp_log hY).symm
         _ < _ := Real.exp_lt_exp.mpr (by
           have ht : Real.log Y < t.val * (2 * (KPCuspLogShape.dimension F : ℝ)) :=
             (div_lt_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2)
               (Nat.cast_pos.mpr (KPCuspLogShape.dimension_pos F hF)))).mp t.property
           simpa only [mul_comm] using ht)⟩
  left_inv r := by
    apply Subtype.ext
    have he := congrArg (fun r : Radius => r.val) ((radius_log_homeomorph F hF).left_inv
      ⟨r.val, lt_trans hY r.property⟩)
    exact he
  right_inv t := by
    apply Subtype.ext
    exact (radius_log_homeomorph F hF).right_inv t.val
  continuous_toFun := (((continuous_subtype_val.log (fun r =>
    ne_of_gt (lt_trans hY r.property))).div_const _)).subtype_mk _
  continuous_invFun := (Real.continuous_exp.comp
    (continuous_const.mul continuous_subtype_val)).subtype_mk _

 def pinned_radial_presentation
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D)
    (w : NumberField.InfinitePlace F) (Y : ℝ) (hY : 0 < Y) :
    KPCuspCharts.CrossQuotient F S × Set.Ioi Y ≃ₜ
      KPCuspCharts.HighQuotient F S (logHeight (F := F) Y) :=
  (Homeomorph.prodCongr (Homeomorph.refl _) (high_radius_log_homeomorph F hF Y hY)).trans
    (sheared_high_presentation G
      (sectionShape F hF w ∘ (radius_log_homeomorph F hF).symm)
      ((sectionShape_continuous F hF w).comp (radius_log_homeomorph F hF).symm.continuous)
      (logHeight (F := F) Y))

private theorem pinned_radial_presentation_formula
    {F : Type} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    (G : KPCuspCharts.ChartOutput F hF S D)
    (w : NumberField.InfinitePlace F) (Y : ℝ) (hY : 0 < Y)
    (p : KPCuspCharts.Cross F) (r : Set.Ioi Y) :
    pinned_radial_presentation G w Y hY (Quotient.mk _ p, r) =
      Quotient.mk _ (⟨((p.1, p.2 + sectionShape F hF w
        ⟨r.val, lt_trans hY r.property⟩), logHeight (F := F) r.val),
          (high_radius_log_homeomorph F hF Y hY r).property⟩ :
        {p : KPCuspCharts.Coordinates F // logHeight (F := F) Y < p.2}) := by
  change sheared_high_presentation G _ _ _
    (Quotient.mk _ p, high_radius_log_homeomorph F hF Y hY r) = _
  rw [sheared_high_presentation_formula]
  congr 1
  apply Subtype.ext
  have he := (radius_log_homeomorph F hF).symm_apply_apply
    (⟨r.val, lt_trans hY r.property⟩ : Radius)
  change (radius_log_homeomorph F hF).symm (logHeight (F := F) r.val) = _ at he
  simp only [Function.comp_apply]
  rw [show (high_radius_log_homeomorph F hF Y hY r).val =
    logHeight (F := F) r.val from rfl, he]

section PinnedLocalEnd
open Topology
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {hF : NumberField.InfinitePlace.nrRealPlaces F = 0} {U : Level F ζ hζ}
variable (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)

 def high_inclusion (j : CuspIndex A) (T : ℝ) (hT : A.threshold ≤ T) :=
  ((Geometry A j).highPresentation A.threshold) ∘
    Prod.map id (Set.inclusion (show Set.Ioi T ⊆ Set.Ioi A.threshold from
      fun _ hx => lt_of_le_of_lt hT hx)) ∘ ((Geometry A j).highPresentation T).symm
private theorem high_inclusion_open (j : CuspIndex A) (T : ℝ) (hT : A.threshold ≤ T) :
    IsOpenEmbedding (high_inclusion A j T hT) := by
  apply (Geometry A j).highPresentation A.threshold |>.isOpenEmbedding.comp
  apply IsOpenEmbedding.comp _ ((Geometry A j).highPresentation T).symm.isOpenEmbedding
  exact IsOpenEmbedding.id.prodMap (.inclusion _ (isOpen_Ioi.preimage continuous_subtype_val))
private theorem high_end_factor (j : CuspIndex A) (T : ℝ) (hT : A.threshold ≤ T) :
    KPFiniteCuspAtlas.endMap F
      (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
      ((A.cuspAtlas j.1).cusp j.2) ((A.cuspAtlas j.1).representative j.2) T =
    KPFiniteCuspAtlas.endMap F
      (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
      ((A.cuspAtlas j.1).cusp j.2) ((A.cuspAtlas j.1).representative j.2) A.threshold ∘
        high_inclusion A j T hT := by
  funext z
  obtain ⟨⟨q,t⟩,rfl⟩ := ((Geometry A j).highPresentation T).surjective z
  dsimp only [Function.comp_apply, high_inclusion]
  rw [Homeomorph.symm_apply_apply]
  induction q using Quotient.inductionOn with
  | h p =>
    dsimp only [Prod.map, id_eq]
    rw [(Geometry A j).highPresentation_formula, (Geometry A j).highPresentation_formula]
    rfl
private theorem high_end_open (j : CuspIndex A) (T : ℝ) (hT : A.threshold ≤ T) :
    IsOpenEmbedding (KPFiniteCuspAtlas.endMap F
      (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
      ((A.cuspAtlas j.1).cusp j.2) ((A.cuspAtlas j.1).representative j.2) T) := by
  rw [high_end_factor A j T hT]
  apply IsOpenEmbedding.comp _ (high_inclusion_open A j T hT)
  refine ⟨?_, ?_⟩
  · have he := (A.cuspAtlas j.1).end_embedding j.2
    rw [A.common_threshold j.1] at he
    exact he
  · rw [KPFiniteCuspAtlas.endMap_range F (Geometry A j).positive_dimension]
    simpa only [A.common_threshold j.1] using (A.cuspAtlas j.1).open_ends j.2

private theorem sigma_open_embedding {ι : Type*} {σ : ι → Type*} {X : Type*}
    [∀ i, TopologicalSpace (σ i)] [TopologicalSpace X]
    (f : (Σ i, σ i) → X)
    (hf : ∀ i, IsOpenEmbedding (fun x => f ⟨i,x⟩))
    (hd : Pairwise (fun i j => Disjoint (Set.range (fun x => f ⟨i,x⟩))
      (Set.range (fun x => f ⟨j,x⟩)))) : IsOpenEmbedding f := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact continuous_sigma (fun i => (hf i).continuous)
  · rintro ⟨i,x⟩ ⟨j,y⟩ he
    by_cases hij : i = j
    · subst j
      exact congrArg (Sigma.mk i) ((hf i).injective he)
    · exact False.elim (Set.disjoint_left.mp (hd hij) (Set.mem_range_self x)
        (show f ⟨i,x⟩ ∈ Set.range (fun y => f ⟨j,y⟩) from ⟨y,he.symm⟩))
  · exact isOpenMap_sigma.mpr (fun i => (hf i).isOpenMap)
private theorem actual_component_open (i : Fin A.componentCount) :
    IsOpenEmbedding (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i)) := by
  have he : KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i) =
      A.components ∘ Sigma.mk i := by
    funext x
    exact (A.components_formula i x).symm
  rw [he]
  exact A.components.isOpenEmbedding.comp IsOpenEmbedding.sigmaMk
private theorem endSet_mono (j : CuspIndex A) {T S : ℝ} (h : S ≤ T) :
    KPFiniteCuspAtlas.endSet F
      (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
      ((A.cuspAtlas j.1).representative j.2) T ⊆
    KPFiniteCuspAtlas.endSet F
      (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
      ((A.cuspAtlas j.1).representative j.2) S := by
  apply Set.image_mono
  apply Set.image_mono
  exact fun _ hx => lt_of_le_of_lt h hx
private theorem component_ends_disjoint (T : ℝ) (hT : A.threshold ≤ T) :
    Pairwise fun j k : CuspIndex A => Disjoint
      (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative j.1) ''
        KPFiniteCuspAtlas.endSet F
          (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
          ((A.cuspAtlas j.1).representative j.2) T)
      (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative k.1) ''
        KPFiniteCuspAtlas.endSet F
          (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative k.1))
          ((A.cuspAtlas k.1).representative k.2) T) := by
  rintro ⟨i,a⟩ ⟨l,b⟩ hne
  apply Set.disjoint_left.mpr
  rintro x ⟨y,hy,rfl⟩ ⟨z,hz,he⟩
  have hec : A.components ⟨l,z⟩ = A.components ⟨i,y⟩ := by
    simpa only [A.components_formula] using he
  have hs := A.components.injective hec
  have hil : l = i := congrArg Sigma.fst hs
  subst l
  have hab : a ≠ b := fun h => hne (congrArg (Sigma.mk i) h)
  have hyz : z = y := by simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using hs
  subst z
  have hd := (A.cuspAtlas i).disjoint_ends hab
  apply Set.disjoint_left.mp hd
  · exact endSet_mono A ⟨i,a⟩ (by rw [A.common_threshold i]; exact hT) hy
  · exact endSet_mono A ⟨i,b⟩ (by rw [A.common_threshold i]; exact hT) hz

private theorem actual_endMap_continuous (j : CuspIndex A) (T : ℝ) :
    Continuous (KPFiniteCuspAtlas.endMap F
      (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
      ((A.cuspAtlas j.1).cusp j.2) ((A.cuspAtlas j.1).representative j.2) T) := by
  apply Continuous.quotient_lift
  exact continuous_quotient_mk'.comp
    (((KPCuspCharts.projectiveHomeomorph F
      ((A.cuspAtlas j.1).representative j.2)).continuous.comp
        (KPCuspCharts.toArch_contDiff F).continuous).comp continuous_subtype_val)

 def pinned_local_end (j : CuspIndex A) (w : NumberField.InfinitePlace F)
    (Y : ℝ) (hY : 0 < Y) :
    KPCuspCharts.CrossQuotient F
      (KPCuspArithmetic.conjugatedStabilizer F
        (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
        ((A.cuspAtlas j.1).cusp j.2) ((A.cuspAtlas j.1).representative j.2)) × Set.Ioi Y →
        Spherical F ζ hζ U :=
  KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative j.1) ∘
    KPFiniteCuspAtlas.endMap F
      (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
      ((A.cuspAtlas j.1).cusp j.2) ((A.cuspAtlas j.1).representative j.2)
      (logHeight (F := F) Y) ∘ pinned_radial_presentation (Geometry A j) w Y hY

private theorem pinned_local_end_continuous (j : CuspIndex A)
    (w : NumberField.InfinitePlace F) (Y : ℝ) (hY : 0 < Y) :
    Continuous (pinned_local_end A j w Y hY) := by
  have hc : Continuous (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative j.1)) := by
    have he : KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative j.1) =
        fun x => A.components ⟨j.1,x⟩ := by
      funext x
      exact (A.components_formula j.1 x).symm
    rw [he]
    exact A.components.continuous.comp continuous_sigmaMk
  exact hc.comp ((actual_endMap_continuous A j _).comp
    (pinned_radial_presentation (Geometry A j) w Y hY).continuous)

private theorem pinned_local_end_range (j : CuspIndex A)
    (w : NumberField.InfinitePlace F) (Y : ℝ) (hY : 0 < Y) :
    Set.range (pinned_local_end A j w Y hY) =
      KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative j.1) ''
        KPFiniteCuspAtlas.endSet F
          (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
          ((A.cuspAtlas j.1).representative j.2) (logHeight (F := F) Y) := by
  change Set.range (_ ∘ _ ∘ _) = _
  rw [Set.range_comp, Set.range_comp,
    (pinned_radial_presentation (Geometry A j) w Y hY).surjective.range_eq,
    Set.image_univ, KPFiniteCuspAtlas.endMap_range F (Geometry A j).positive_dimension]

private theorem pinned_local_end_formula (j : CuspIndex A)
    (w : NumberField.InfinitePlace F) (Y : ℝ) (hY : 0 < Y)
    (p : KPCuspCharts.Cross F) (r : Set.Ioi Y) :
    pinned_local_end A j w Y hY (Quotient.mk _ p,r) =
      KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative j.1)
        (KPCuspSiegel.projection F
          (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
          (((A.cuspAtlas j.1).representative j.2) • KPCuspCharts.toArch F
            ((p.1, p.2 + sectionShape F hF w ⟨r.val, lt_trans hY r.property⟩),
              logHeight (F := F) r.val))) := by
  dsimp only [pinned_local_end, Function.comp_apply]
  rw [pinned_radial_presentation_formula]
  rfl
private theorem pinned_local_end_open (j : CuspIndex A)
    (w : NumberField.InfinitePlace F) (Y : ℝ) (hY : AdmissibleCutoff A Y) :
    IsOpenEmbedding (pinned_local_end A j w Y hY.1) :=
  (actual_component_open A j.1).comp
    ((high_end_open A j _ hY.2).comp
      (pinned_radial_presentation (Geometry A j) w Y hY.1).isOpenEmbedding)

 def pinned_cusp_chart (w : NumberField.InfinitePlace F)
    (Y : ℝ) (hY : 0 < Y) : CrossSection A × Set.Ioi Y → Spherical F ζ hζ U :=
  (fun x => pinned_local_end A x.1 w Y hY x.2) ∘ Homeomorph.sigmaProdDistrib

private theorem pinned_cusp_chart_continuous (w : NumberField.InfinitePlace F)
    (Y : ℝ) (hY : 0 < Y) : Continuous (pinned_cusp_chart A w Y hY) := by
  apply Continuous.comp _ Homeomorph.sigmaProdDistrib.continuous
  apply continuous_sigma
  intro j
  exact pinned_local_end_continuous A j w Y hY

private theorem pinned_cusp_chart_range (w : NumberField.InfinitePlace F)
    (Y : ℝ) (hY : 0 < Y) :
    Set.range (pinned_cusp_chart A w Y hY) = cuspEnds A Y := by
  ext x
  change (∃ p : CrossSection A × Set.Ioi Y, pinned_cusp_chart A w Y hY p = x) ↔ _
  simp only [cuspEnds, Set.mem_iUnion]
  constructor
  · rintro ⟨⟨⟨j,p⟩,r⟩, he⟩
    refine ⟨j, ?_⟩
    rw [← pinned_local_end_range A j w Y hY]
    exact ⟨(p,r), he⟩
  · rintro ⟨j, hx⟩
    rw [← pinned_local_end_range A j w Y hY] at hx
    obtain ⟨⟨p,r⟩,he⟩ := hx
    exact ⟨(⟨j,p⟩,r), he⟩

private theorem pinned_cusp_chart_open (w : NumberField.InfinitePlace F)
    (Y : ℝ) (hY : AdmissibleCutoff A Y) :
    IsOpenEmbedding (pinned_cusp_chart A w Y hY.1) := by
  apply IsOpenEmbedding.comp _ Homeomorph.sigmaProdDistrib.isOpenEmbedding
  apply sigma_open_embedding
  · intro j
    exact pinned_local_end_open A j w Y hY
  · simpa only [pinned_local_end_range] using
      component_ends_disjoint A (logHeight (F := F) Y) hY.2

private theorem pinned_cusp_chart_embedding (w : NumberField.InfinitePlace F)
    (Y : ℝ) (hY : AdmissibleCutoff A Y) :
    IsEmbedding (pinned_cusp_chart A w Y hY.1) :=
  (pinned_cusp_chart_open A w Y hY).isEmbedding

 theorem pinned_cusp_chart_formula (w : NumberField.InfinitePlace F)
    (Y : ℝ) (hY : 0 < Y) (j : CuspIndex A)
    (p : KPCuspCharts.Cross F) (r : Set.Ioi Y) :
    pinned_cusp_chart A w Y hY (⟨j, Quotient.mk _ p⟩,r) =
      KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative j.1)
        (KPCuspSiegel.projection F
          (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
          (((A.cuspAtlas j.1).representative j.2) • KPCuspCharts.toArch F
            ((p.1, p.2 + sectionShape F hF w ⟨r.val, lt_trans hY r.property⟩),
              logHeight (F := F) r.val))) :=
  pinned_local_end_formula A j w Y hY p r

 def base_cutoff : ℝ :=
  Real.exp (2 * (KPCuspLogShape.dimension F : ℝ) * A.threshold)

 theorem base_cutoff_admissible : AdmissibleCutoff A (base_cutoff A) := by
  refine ⟨Real.exp_pos _, ?_⟩
  unfold logHeight base_cutoff
  rw [Real.log_exp, mul_div_cancel_left₀ _ (ne_of_gt (mul_pos (by norm_num)
    (Nat.cast_pos.mpr (KPCuspLogShape.dimension_pos F hF))))]

private theorem base_cutoff_le (Y : ℝ) (hY : AdmissibleCutoff A Y) :
    base_cutoff A ≤ Y := by
  unfold base_cutoff
  rw [← Real.exp_log hY.1]
  apply Real.exp_le_exp.mpr
  have hd : 0 < 2 * (KPCuspLogShape.dimension F : ℝ) :=
    mul_pos (by norm_num) (Nat.cast_pos.mpr (KPCuspLogShape.dimension_pos F hF))
  have ht := (le_div_iff₀ hd).mp hY.2
  simpa only [mul_comm] using ht

private theorem pinned_cusp_chart_cutoff (w : NumberField.InfinitePlace F)
    (Y Z : ℝ) (hY : 0 < Y) (hZ : 0 < Z) (x : CrossSection A)
    (r : Set.Ioi Y) (hr : Z < r.val) :
    pinned_cusp_chart A w Y hY (x,r) =
      pinned_cusp_chart A w Z hZ (x,⟨r.val,hr⟩) := by
  rcases x with ⟨j,x⟩
  induction x using Quotient.inductionOn with
  | h p =>
    rw [pinned_cusp_chart_formula, pinned_cusp_chart_formula]

 def pinned_modulus (w : NumberField.InfinitePlace F) :
    Spherical F ζ hζ U → ℝ :=
  Function.extend (pinned_cusp_chart A w (base_cutoff A) (base_cutoff_admissible A).1)
    (fun p => p.2.val) (fun _ => 0)

private theorem pinned_modulus_measurable (w : NumberField.InfinitePlace F) :
    Measurable (pinned_modulus A w) := by
  apply (pinned_cusp_chart_open A w _ (base_cutoff_admissible A)).measurableEmbedding.measurable_extend
  · exact measurable_subtype_coe.comp measurable_snd
  · exact measurable_const

private theorem pinned_modulus_base (w : NumberField.InfinitePlace F)
    (x : CrossSection A) (r : Set.Ioi (base_cutoff A)) :
    pinned_modulus A w
      (pinned_cusp_chart A w (base_cutoff A) (base_cutoff_admissible A).1 (x,r)) = r.val := by
  exact (pinned_cusp_chart_embedding A w _ (base_cutoff_admissible A)).injective.extend_apply
    (fun p => p.2.val) (fun _ => 0) (x,r)

private theorem pinned_cusp_chart_modulus (w : NumberField.InfinitePlace F)
    (Y : ℝ) (hY : AdmissibleCutoff A Y) (x : CrossSection A) (r : Set.Ioi Y) :
    pinned_modulus A w (pinned_cusp_chart A w Y hY.1 (x,r)) = r.val := by
  have hr : base_cutoff A < r.val := lt_of_le_of_lt (base_cutoff_le A Y hY) r.property
  rw [pinned_cusp_chart_cutoff A w Y (base_cutoff A) hY.1
    (base_cutoff_admissible A).1 x r hr]
  exact pinned_modulus_base A w x ⟨r.val,hr⟩

end PinnedLocalEnd

end PinnedRadialCharts

namespace ComponentNormalization
open MeasureTheory Set
open scoped ENNReal Pointwise

private theorem smul_weight_unique
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (A : Set X)
    (hz : μ A ≠ 0) (ht : μ A ≠ ⊤) {a b : ℝ≥0∞}
    (h : a • μ = b • μ) : a = b := by
  have he := congrArg (fun ν : Measure X => ν A) h
  simp only [Measure.smul_apply, smul_eq_mul] at he
  exact (ENNReal.mul_right_inj hz ht).mp (by simpa only [mul_comm] using he)

end ComponentNormalization

namespace ComponentFiber
open _root_.DedekindZetaZeroFree.KPActualComponentHaarSources renaming basepoint_continuous → basepoint_continuous
open MeasureTheory Set
open scoped ENNReal Pointwise
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

private theorem finite_orbit_spherical (U : Level F ζ hζ)
    (g c : KPFiniteCuspAtlas.FiniteCover F ζ hζ)
    (hc : c ∈ KPCuspGenuineMonodromy.finiteOrbit F ζ hζ U g)
    (x : KPFiniteCuspAtlas.SymmetricSpace F) :
    (Quotient.mk (KPFiniteCuspAtlas.sphericalRelation F ζ hζ U) (x,c) : Spherical F ζ hζ U) =
      KPFiniteCuspAtlas.componentMap F ζ hζ U g (KPCuspSiegel.projection F _ x) := by
  obtain ⟨ε,u,rfl⟩ := hc
  change Quotient.mk _ (x,_) = Quotient.mk _ (x,g)
  apply Eq.symm
  apply Quotient.sound
  refine ⟨1, ε, u, ?_, ?_⟩
  · simp
  · simp

 theorem spherical_fiber_formula (P : SphericalTransport F ζ hζ) (U : Level F ζ hζ)
    (g c : KPFiniteCuspAtlas.FiniteCover F ζ hζ)
    (hc : c ∈ KPCuspGenuineMonodromy.finiteOrbit F ζ hζ U g)
    (a : KPSmoothActualFlowData.GInfinity F) :
    P.projection U (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * c.val)) =
      KPFiniteCuspAtlas.componentMap F ζ hζ U g
        (KPCuspSiegel.projection F _ (archBasepoint F a)) := by
  rw [P.formula]
  exact finite_orbit_spherical F ζ hζ U g c hc _

private theorem spherical_restrict_pushforward
    {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : SphericalTransport F ζ hζ) (U : Level F ζ hζ)
    (C : Set (Spherical F ζ hζ U)) (hC : MeasurableSet C) :
    (sphericalMeasure F ζ hζ R P U).restrict C =
      Measure.map (P.projection U) (R.quotientHaar.restrict (P.projection U ⁻¹' C)) := by
  exact Measure.restrict_map (P.continuous U).measurable hC

private theorem component_range_clopen
    {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0} {U : Level F ζ hζ}
    (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U) (i : Fin A.componentCount) :
    IsClopen (Set.range (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i))) := by
  have he : KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i) =
      A.components ∘ Sigma.mk i := by
    funext x
    exact (A.components_formula i x).symm
  rw [he, Set.range_comp]
  constructor
  · exact A.components.isClosedMap _ isClosed_range_sigmaMk
  · exact A.components.isOpenMap _ isOpen_range_sigmaMk

private theorem actual_component_weight
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {U : Level F ζ hζ} (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : SphericalTransport F ζ hζ) (i : Fin A.componentCount) :
    ∃ w : ℝ≥0∞, 0 < w ∧ w < ⊤ ∧
      (sphericalMeasure F ζ hζ R P U).restrict
        (Set.range (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i))) =
      w • Measure.map (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i))
        (KPFiniteCuspAtlas.quotientVolume F
          (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative i))
          (A.cuspAtlas i).fundamentalDomain) := by
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.2
  letI := ActualQuotient.actual_cover_secondCountable F ζ hζ
  letI : BorelSpace (KPSmoothActualFlowData.GInfinity F) := ⟨rfl⟩
  letI : SecondCountableTopology (KPFiniteCuspAtlas.FiniteCover F ζ hζ) := by
    change SecondCountableTopology ↥((KPCuspGenuineMonodromy.archProjection F ζ hζ).ker : Set (KPCuspGenuineMonodromy.Cover F ζ hζ))
    infer_instance
  obtain ⟨ep,hep,_,_,_,_,hLCP⟩ := PGLComplex.AdelicSlicesRaw.actualArchFiniteSplitting F ζ hζ
  letI : SecondCountableTopology (PGLComplex.AdelicSlicesRaw.ArchGroup F × PGLComplex.AdelicSlicesRaw.finiteSubgroup F ζ hζ) := by
    letI : SecondCountableTopology (PGLComplex.AdelicSlicesRaw.ActualCover F ζ hζ) := ActualQuotient.actual_cover_secondCountable F ζ hζ
    exact ep.toHomeomorph.secondCountableTopology
  letI : SecondCountableTopology (KPSmoothActualFlowData.GInfinity F) :=
    (isEmbedding_prodMkLeft (1 : PGLComplex.AdelicSlicesRaw.finiteSubgroup F ζ hζ)).secondCountableTopology
  letI : BorelSpace (KPSmoothActualFlowData.GInfinity F × KPFiniteCuspAtlas.FiniteCover F ζ hζ) := inferInstance
  obtain ⟨ν,hν,hprod,D,hDm,hD,hB,hBp,hBf,hq⟩ :=
    KPActualComponentHaarSources.actual_component_product_disintegration F ζ hζ hF U A R P i
  obtain ⟨c,hc,harch,hvol⟩ :=
    KPActualComponentHaarSources.arch_group_domain_quotient_volume F ζ hζ hF U A R i D hDm hD
  letI := hν
  letI := R.arch_isHaar
  letI : LocallyCompactSpace (KPSmoothActualFlowData.GInfinity F) := by
    obtain ⟨e,he,_,_,_,_,hLC⟩ := PGLComplex.AdelicSlicesRaw.actualArchFiniteSplitting F ζ hζ
    letI : LocallyCompactSpace (PGLComplex.AdelicSlicesRaw.ActualCover F ζ hζ) := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.1
    letI : LocallyCompactSpace (PGLComplex.AdelicSlicesRaw.ArchGroup F × PGLComplex.AdelicSlicesRaw.finiteSubgroup F ζ hζ) := e.toHomeomorph.isClosedEmbedding.locallyCompactSpace
    exact (isOpenQuotientMap_fst (Y := PGLComplex.AdelicSlicesRaw.finiteSubgroup F ζ hζ)).locallyCompactSpace
  let BB := KPActualComponentHaarSources.B F ζ hζ hF U A i
  letI : IsFiniteMeasure (ν.restrict BB) := ⟨by simpa [BB] using hBf⟩
  letI : SFinite R.archHaar := inferInstance
  refine ⟨ν (KPActualComponentHaarSources.B F ζ hζ hF U A i) * c,
    ENNReal.mul_pos hBp.ne' (ENNReal.coe_pos.mpr hc).ne', ENNReal.mul_lt_top hBf ENNReal.coe_lt_top, ?_⟩
  rw [spherical_restrict_pushforward R P U _ (component_range_clopen A i).isOpen.measurableSet,
    ]
  unfold KPActualComponentHaarSources.C at hq
  rw [hq]
  have hcm : Measurable (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i)) := by
    have he : KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i) =
        A.components ∘ Sigma.mk i := by funext x; exact (A.components_formula i x).symm
    apply measurable_from_quotient.mpr
    have hh : Measurable (fun x : KPFiniteCuspAtlas.SymmetricSpace F => A.components ⟨i, KPCuspSiegel.projection F (KPActualComponentHaarSources.Gi F ζ hζ hF U A i) x⟩) :=
      (A.components.continuous.comp ((continuous_sigmaMk (i := i)).comp
        (continuous_quotient_mk' : Continuous (KPCuspSiegel.projection F (KPActualComponentHaarSources.Gi F ζ hζ hF U A i))))).measurable
    convert hh using 1
    funext x
    exact (A.components_formula i (KPCuspSiegel.projection F _ x)).symm
  have hb : Measurable (KPCuspSiegel.projection F
      (KPActualComponentHaarSources.Gi F ζ hζ hF U A i) ∘ archBasepoint F) := by
    exact measurable_quotient_mk''.comp (basepoint_continuous F ζ hζ).measurable
  let f := KPSmoothLocalQuotientCharts.quotientMap F ζ hζ ∘ KPActualComponentHaarSources.m F ζ hζ
  let gg := KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i) ∘
    KPCuspSiegel.projection F (KPActualComponentHaarSources.Gi F ζ hζ hF U A i) ∘ archBasepoint F
  have hfm : Measurable f := by
    apply Continuous.measurable
    exact continuous_quotient_mk'.comp
      (((KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.1.comp
        continuous_fst).mul (continuous_subtype_val.comp continuous_snd))
  rw [Measure.map_map (P.continuous U).measurable hfm]
  have he : (P.projection U ∘ f) =ᵐ[(R.archHaar.restrict D).prod (ν.restrict BB)] gg ∘ Prod.fst := by
    have hmem : ∀ᵐ p ∂(R.archHaar.restrict D).prod (ν.restrict BB), p.2 ∈ BB :=
      (Measure.ae_prod_iff_ae_ae (measurable_snd hB)).mpr
        (Filter.Eventually.of_forall fun _ => ae_restrict_mem hB)
    filter_upwards [hmem] with p hp
    exact spherical_fiber_formula F ζ hζ P U (A.representative i) p.2 hp p.1
  rw [Measure.map_congr he, ← Measure.map_map (hcm.comp hb) measurable_fst,
    Measure.map_fst_prod, Measure.restrict_apply_univ,
    Measure.map_smul _ (hcm.comp hb).aemeasurable]
  have hvol' : Measure.map (KPCuspSiegel.projection F (KPActualComponentHaarSources.Gi F ζ hζ hF U A i) ∘ archBasepoint F) (R.archHaar.restrict D) = (c : ℝ≥0∞) • KPFiniteCuspAtlas.quotientVolume F (KPActualComponentHaarSources.Gi F ζ hζ hF U A i) (A.cuspAtlas i).fundamentalDomain := hvol
  simp only [← Measure.map_map hcm hb, hvol', Measure.map_smul _ hcm.aemeasurable, smul_smul]
  rfl

private theorem actual_component_weights
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {U : Level F ζ hζ} (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : SphericalTransport F ζ hζ) :
    ∃ w : Fin A.componentCount → ℝ≥0∞, (∀ i, 0 < w i) ∧ (∀ i, w i < ⊤) ∧
      ∀ i, (sphericalMeasure F ζ hζ R P U).restrict
        (Set.range (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i))) =
      w i • Measure.map (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative i))
        (KPFiniteCuspAtlas.quotientVolume F
          (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative i))
          (A.cuspAtlas i).fundamentalDomain) := by
  choose w hp hf he using fun i => actual_component_weight F ζ hζ A R P i
  exact ⟨w,hp,hf,he⟩

end ComponentFiber

namespace FixedLevelGeometry
open MeasureTheory

 theorem actual_fixed_level_geometry
    {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {U : Level F ζ hζ} (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : SphericalTransport F ζ hζ) (B : RadialData F ζ hζ) (K : FiberKernel A) :
    ∃ D : GeometricDisintegration A R P, D.radial = B := by
  obtain ⟨w,hpos,hfin,hcomp⟩ := ComponentFiber.actual_component_weights F ζ hζ A R P
  refine ⟨{
    toFiberKernel := K
    radial := B
    beta := weighted_angular_measure A w
    finite_beta := weighted_angular_finite A w hfin
    positive_beta := weighted_angular_positive A w hpos
    probability_mass := weighted_angular_probability A w hpos hfin
    componentWeight := w
    positive_componentWeight := hpos
    finite_componentWeight := hfin
    component_measure := hcomp
    section_disintegration := weighted_section_disintegration A K w
    modulus := PinnedRadialCharts.pinned_modulus A B.slot
    measurable_modulus := PinnedRadialCharts.pinned_modulus_measurable A B.slot
    chart := fun Y hY => PinnedRadialCharts.pinned_cusp_chart A B.slot Y hY.1
    measurable_chart := fun Y hY =>
      (PinnedRadialCharts.pinned_cusp_chart_continuous A B.slot Y hY.1).measurable
    chart_range := fun Y hY => PinnedRadialCharts.pinned_cusp_chart_range A B.slot Y hY.1
    chart_embedding := fun Y hY => PinnedRadialCharts.pinned_cusp_chart_embedding A B.slot Y hY
    chart_modulus := fun Y hY => PinnedRadialCharts.pinned_cusp_chart_modulus A B.slot Y hY
    chart_formula := fun Y hY => PinnedRadialCharts.pinned_cusp_chart_formula A B.slot Y hY.1
    }, rfl⟩

end FixedLevelGeometry

end DedekindZetaZeroFree.KPMsFixedHaar

end
