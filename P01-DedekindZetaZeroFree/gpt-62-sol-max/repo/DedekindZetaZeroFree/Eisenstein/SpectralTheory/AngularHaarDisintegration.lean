module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CoherentPinnedCuspGeometry

@[expose] public section

section

noncomputable section

open scoped Classical NumberField ENNReal NNReal

open MeasureTheory

namespace DedekindZetaZeroFree

namespace KPMsFixedHaarDisintegration

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

export KPMsFixedHaar (Level Spherical)

end KPMsFixedHaarDisintegration

end DedekindZetaZeroFree

end

end

section

noncomputable section
open scoped Classical NumberField ENNReal NNReal
open MeasureTheory

namespace DedekindZetaZeroFree.KPMsFixedHaar
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem fixed_haar_recipe
    (μ : Measure (KPCubicCoverConstruction.AdelicPGL2Cover F ζ hζ))
    (hμ : μ.IsHaarMeasure) :
    ∃ R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ,
      R.adelicHaar = μ ∧ R.quotientHaar.IsOpenPosMeasure := by

  obtain ⟨e, he, hep, hip, hker, hcen, hlc⟩ :=
    PGLComplex.AdelicSlicesRaw.actualArchFiniteSplitting F ζ hζ
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).1
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.1
  letI := (ActualQuotient.actual_cover_lc_t2_group F ζ hζ).2.2
  letI : LocallyCompactSpace
      (PGLComplex.AdelicSlicesRaw.ArchGroup F ×
        ↥(PGLComplex.AdelicSlicesRaw.finiteSubgroup F ζ hζ)) :=
    e.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  letI : LocallyCompactSpace (KPSmoothLocalQuotientCharts.ArchGroup F) :=
    (isOpenQuotientMap_fst (Y := PGLComplex.AdelicSlicesRaw.finiteSubgroup F ζ hζ)).locallyCompactSpace
  letI : BorelSpace (KPSmoothLocalQuotientCharts.ArchGroup F) := ⟨rfl⟩
  let archHaar : Measure (KPSmoothLocalQuotientCharts.ArchGroup F) := MeasureTheory.Measure.haar
  have arch_isHaar : archHaar.IsHaarMeasure := inferInstance

  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI : Countable (Matrix (Fin 2) (Fin 2) F) :=
    inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
  letI : Countable (KubotaRankTwo.GL2 F) := Units.val_injective.countable
  letI : Countable (KPRationalAdelicSplitting.RationalPGL2 F) :=
    (Quotient.mk'_surjective (s := QuotientGroup.leftRel
      (KPRationalAdelicSplitting.rationalScalars F))).countable
  letI : Countable (KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ) :=
    Set.Countable.to_subtype (Set.countable_range
      (KPSmoothLocalQuotientCharts.rationalSplit F ζ hζ))
  have hdisc : DiscreteTopology (KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ) :=
    SetLike.isDiscrete_iff_discreteTopology.mp
      (ActualQuotient.actual_rational_closed_discrete F ζ hζ).2
  letI : SecondCountableTopology (Cover F ζ hζ) :=
    ActualQuotient.actual_cover_secondCountable F ζ hζ

  haveI : ProperlyDiscontinuousSMul (KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ)
      (Cover F ζ hζ) := by
    have hH : IsCompact (MulAction.stabilizer (Cover F ζ hζ)
        (1 : Cover F ζ hζ) : Set (Cover F ζ hζ)) := by
      have h : MulAction.stabilizer (Cover F ζ hζ) (1 : Cover F ζ hζ) = ⊥ := by
        ext g; simp [MulAction.mem_stabilizer_iff]
      rw [h]; exact isCompact_singleton
    exact KPArithmeticAction.properlyDiscontinuous_of_section (1 : Cover F ζ hζ) id
      continuous_id (fun x => by simp) hH (KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ)

  have hfree : ∀ᵐ x ∂μ, ∀ g : KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ,
      g • x = x → g = 1 := by
    refine Filter.Eventually.of_forall fun x g hg => ?_
    have h2 : (g : Cover F ζ hζ) * x = x := hg
    have : (g : Cover F ζ hζ) = 1 := by
      simp_all
    exact Subtype.ext this
  obtain ⟨Ω, hΩmeas, hΩfund⟩ :=
    KPCuspChart.SectionConstruction.measurable_fundamental_domain_of_properly_discontinuous_ae_free
      (H := KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ) (X := Cover F ζ hζ) μ hfree
  let R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ := {
    adelicHaar := μ
    adelic_isHaar := hμ
    archHaar := archHaar
    arch_isHaar := arch_isHaar
    quotientHaar := Measure.map (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ) (μ.restrict Ω)
    domain := Ω
    domain_measurable := hΩmeas
    domain_fundamental := hΩfund
    quotient_normalization := rfl }
  exact ⟨R, rfl, (KPSmoothLocalQuotientCharts.quotient_full_support F ζ hζ R).1⟩

end DedekindZetaZeroFree.KPMsFixedHaar

end
end

section

noncomputable section
open scoped Classical NumberField ENNReal
open MeasureTheory
namespace DedekindZetaZeroFree.KPMsFixedHaar

private theorem affine_probability_haar
    {T : Type*} [AddCommGroup T] [TopologicalSpace T] [IsTopologicalAddGroup T]
    [MeasurableSpace T] [BorelSpace T] [LocallyCompactSpace T]
    (e : T ≃ₜ T) (he : ∀ x y, e (x + y) = e x + e y - e 0)
    (ν : Measure T) [ν.IsAddHaarMeasure] [IsProbabilityMeasure ν] :
    Measure.map e ν = ν := by
  let h : T ≃ₜ T := e.trans (Homeomorph.subRight (e 0))
  let a : T ≃ₜ+ T := {
    toHomeomorph := h
    map_add' := fun x y => by
      change e (x + y) - e 0 = (e x - e 0) + (e y - e 0)
      rw [he]
      abel }
  haveI : (Measure.map a ν).IsAddHaarMeasure := a.isAddHaarMeasure_map ν
  haveI : IsProbabilityMeasure (Measure.map a ν) :=
    Measure.isProbabilityMeasure_map_iff a.continuous.measurable.aemeasurable |>.mpr inferInstance
  have ha : Measure.map a ν = ν := Measure.isAddHaarMeasure_eq_of_isProbabilityMeasure _ _
  have hcomp : (fun x => e 0 + a x) = e := by
    funext x
    change e 0 + (e x - e 0) = e x
    abel
  rw [← hcomp]
  change Measure.map ((fun x => e 0 + x) ∘ a) ν = ν
  rw [← Measure.map_map (show Measurable (fun x : T => e 0 + x) from
    (continuous_const.add continuous_id).measurable)
    (show Measurable (a : T → T) from a.continuous.measurable), ha]
  exact Measure.IsAddLeftInvariant.map_add_left_eq_self _

theorem torusAction_probability_haar
    {F : Type*} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} (D : KPCuspCharts.ParabolicData F S)
    (G : KPCuspCharts.ChartOutput F hF S D)
    [MeasurableSpace (KPCuspCharts.Torus F D.L)]
    [BorelSpace (KPCuspCharts.Torus F D.L)]
    [LocallyCompactSpace (KPCuspCharts.Torus F D.L)]
    (ν : Measure (KPCuspCharts.Torus F D.L))
    [ν.IsAddHaarMeasure] [IsProbabilityMeasure ν] (u : D.E) :
    Measure.map (G.torusAction u) ν = ν := by
  apply affine_probability_haar
  obtain ⟨g, rfl⟩ := D.surjective u
  obtain ⟨M, hM, hc⟩ := D.upper g g.property
  intro z w
  induction z using QuotientAddGroup.induction_on with | H x =>
    induction w using QuotientAddGroup.induction_on with | H y =>
      rw [← QuotientAddGroup.mk_add]
      change G.torusAction (D.ratio g) (QuotientAddGroup.mk (x + y)) =
        G.torusAction (D.ratio g) (QuotientAddGroup.mk x) +
          G.torusAction (D.ratio g) (QuotientAddGroup.mk y) -
            G.torusAction (D.ratio g) (QuotientAddGroup.mk 0)
      simp only [G.torusAction_formula g M _ hM hc]
      rw [← QuotientAddGroup.mk_add, ← QuotientAddGroup.mk_sub]
      congr 1
      funext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply]
      ring

private theorem measurable_of_countable_open_cover
    {I X Y : Type*} [Countable I] [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y]
    (s : I → Set X) (hs : ∀ i, IsOpen (s i)) (hc : (⋃ i, s i) = Set.univ)
    (f : X → Y) (hf : ∀ i, Measurable (fun x : s i => f x.val)) : Measurable f := by
  intro E hE
  have heq : f ⁻¹' E = ⋃ i, Subtype.val '' ((fun x : s i => f x.val) ⁻¹' E) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_image, Subtype.exists,
      exists_and_right, exists_eq_right]
    constructor
    · intro hx
      have : x ∈ ⋃ i, s i := by rw [hc]; trivial
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp this
      exact ⟨i, hi, hx⟩
    · rintro ⟨i, hi, hx⟩
      exact hx
  rw [heq]
  exact MeasurableSet.iUnion fun i =>
    (hs i).isOpenEmbedding_subtypeVal.measurableEmbedding.measurableSet_image.mpr (hf i hE)

private theorem measurable_on_sigma
    {I Y : Type*} {X : I → Type*} [Countable I]
    [∀ i, TopologicalSpace (X i)] [∀ i, MeasurableSpace (X i)]
    [∀ i, BorelSpace (X i)] [MeasurableSpace (Sigma X)] [BorelSpace (Sigma X)]
    [MeasurableSpace Y] (f : Sigma X → Y)
    (hf : ∀ i, Measurable (fun x : X i => f ⟨i,x⟩)) : Measurable f := by
  intro E hE
  have heq : f ⁻¹' E = ⋃ i, Sigma.mk i '' ((fun x : X i => f ⟨i,x⟩) ⁻¹' E) := by
    ext ⟨i,x⟩
    constructor
    · intro hx
      exact Set.mem_iUnion.mpr ⟨i, ⟨x, hx, rfl⟩⟩
    · intro hx
      obtain ⟨j, y, hy, he⟩ := Set.mem_iUnion.mp hx
      change f ⟨j,y⟩ ∈ E at hy
      change f ⟨i,x⟩ ∈ E
      rw [he] at hy
      exact hy
  rw [heq]
  exact MeasurableSet.iUnion fun i =>
    (Topology.IsOpenEmbedding.sigmaMk (i := i)).measurableEmbedding.measurableSet_image.mpr
      (hf i hE)

local instance torusMeasurable (F : Type*) [Field F] [NumberField F] (L : AddSubgroup F) :
    MeasurableSpace (KPCuspCharts.Torus F L) := Quotient.instMeasurableSpace
local instance torusBorel (F : Type*) [Field F] [NumberField F] (L : AddSubgroup F)
    [IsClosed (KPCuspCharts.translationLattice F L : Set (KPCuspCharts.Horizontal F))] :
    BorelSpace (KPCuspCharts.Torus F L) := QuotientAddGroup.borelSpace
local instance baseMeasurable (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (E : Subgroup Fˣ) (hE : E ≤ KPCuspArithmetic.rationalUnits F) :
    MeasurableSpace (KPCuspCharts.Base F hF E hE) := borel _
local instance baseBorel (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (E : Subgroup Fˣ) (hE : E ≤ KPCuspArithmetic.rationalUnits F) :
    BorelSpace (KPCuspCharts.Base F hF E hE) := ⟨rfl⟩

private theorem probability_torus_haar
    {F : Type*} [Field F] [NumberField F]
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} (D : KPCuspCharts.ParabolicData F S)
    (G : KPCuspCharts.ChartOutput F hF S D) :
    ∃ ν : Measure (KPCuspCharts.Torus F D.L), ν.IsAddHaarMeasure ∧ IsProbabilityMeasure ν := by
  obtain ⟨hd, _⟩ := G.lattice
  haveI : DiscreteTopology (KPCuspCharts.translationLattice F D.L) := hd
  haveI : IsClosed (KPCuspCharts.translationLattice F D.L : Set (KPCuspCharts.Horizontal F)) :=
    AddSubgroup.isClosed_of_discreteTopology
  haveI : CompactSpace (KPCuspCharts.Torus F D.L) := G.compact_torus
  let ν : Measure (KPCuspCharts.Torus F D.L) := Measure.addHaarMeasure ⊤
  refine ⟨ν, inferInstance, ⟨?_⟩⟩
  exact Measure.addHaarMeasure_self (K₀ := ⊤)

theorem probability_fiber_kernel
    {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {U : Level F ζ hζ} (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U) :
    Nonempty (FiberKernel A) := by
  classical
  let D := fun j : CuspIndex A => Parabolic A j
  let G := fun j : CuspIndex A => Geometry A j
  choose ν hν hp using fun j : CuspIndex A => probability_torus_haar (D j) (G j)
  haveI (j : CuspIndex A) : (ν j).IsAddHaarMeasure := hν j
  haveI (j : CuspIndex A) : IsProbabilityMeasure (ν j) := hp j
  haveI (j : CuspIndex A) : DiscreteTopology (KPCuspCharts.translationLattice F (D j).L) :=
    (G j).lattice.choose
  haveI (j : CuspIndex A) : IsClosed
      (KPCuspCharts.translationLattice F (D j).L : Set (KPCuspCharts.Horizontal F)) :=
    AddSubgroup.isClosed_of_discreteTopology
  haveI (j : CuspIndex A) : LocallyCompactSpace (KPCuspCharts.Torus F (D j).L) :=
    QuotientAddGroup.instLocallyCompactSpace _
  let φ := fun (j : CuspIndex A) (b : KPCuspCharts.Shape F)
    (z : KPCuspCharts.Torus F (D j).L) =>
      (⟨j, (G j).atlas.lift (z,b)⟩ : CrossSection A)
  have hφ (j : CuspIndex A) (b : KPCuspCharts.Shape F) : Measurable (φ j b) := by
    apply Continuous.measurable
    exact (continuous_sigmaMk (σ := fun k : CuspIndex A =>
      KPCuspCharts.CrossQuotient F (KPCuspArithmetic.conjugatedStabilizer F
        (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative k.1))
        ((A.cuspAtlas k.1).cusp k.2) ((A.cuspAtlas k.1).representative k.2)))
      (i := j)).comp
      ((G j).atlas.continuous_lift.comp (continuous_id.prodMk continuous_const))
  have hmap (j : CuspIndex A) (b b' : KPCuspCharts.Shape F)
      (hb : (QuotientAddGroup.mk b : KPCuspCharts.Base F hF (D j).E
        (D j).integralUnits) = QuotientAddGroup.mk b') :
      Measure.map (φ j b) (ν j) = Measure.map (φ j b') (ν j) := by
    have hm := QuotientAddGroup.eq_iff_sub_mem.mp hb.symm
    change b' - b ∈ (KPCuspLogShape.logarithm F hF (D j).E (D j).integralUnits).range at hm
    obtain ⟨u, hu⟩ := AddMonoidHom.mem_range.mp hm
    have hb' : b' = b + KPCuspLogShape.logarithm F hF (D j).E
        (D j).integralUnits u := by rw [hu]; abel
    have heq : φ j b = φ j b' ∘ (G j).torusAction u.toMul := by
      funext z
      apply congrArg (Sigma.mk j)
      exact ((G j).atlas.orbit_equivalence z _ b b').mpr ⟨u.toMul, rfl, hb'⟩
    rw [heq, ← Measure.map_map (hφ j b') ((G j).torusAction u.toMul).measurable,
      torusAction_probability_haar (D j) (G j) (ν j) u.toMul]
  let K : Omega A → Measure (CrossSection A) := fun ω => Measure.map (φ ω.1 ω.2.out) (ν ω.1)
  have hformula (j : CuspIndex A) (b : KPCuspCharts.Shape F) :
      K ⟨j, QuotientAddGroup.mk b⟩ = Measure.map (φ j b) (ν j) := by
    apply hmap
    exact Quotient.out_eq _
  have hprob (ω : Omega A) : IsProbabilityMeasure (K ω) :=
    Measure.isProbabilityMeasure_map_iff (hφ ω.1 ω.2.out).aemeasurable |>.mpr inferInstance
  refine ⟨{ unipotent := K
            probability_unipotent := hprob
            fiber_support := ?_
            measurable_kernel := ?_
            fiber_formula := fun j b => ⟨ν j, hν j, hp j, hformula j b⟩ }⟩
  · intro ω
    haveI := hprob ω
    apply le_antisymm prob_le_one
    have hpφ (z : KPCuspCharts.Torus F (D ω.1).L) :
        angularProjection A (φ ω.1 ω.2.out z) = ω := by
      induction z using QuotientAddGroup.induction_on with | H x =>
        change (⟨ω.1, (G ω.1).atlas.projection
          ((G ω.1).atlas.lift (QuotientAddGroup.mk x, ω.2.out))⟩ : Omega A) = ω
        rw [(G ω.1).atlas.lift_formula, (G ω.1).atlas.projection_formula]
        exact congrArg (Sigma.mk ω.1) (Quotient.out_eq _)
    have heq : φ ω.1 ω.2.out ⁻¹' {x | angularProjection A x = ω} = Set.univ :=
      Set.eq_univ_of_forall hpφ
    have hm := Measure.le_map_apply (μ := ν ω.1) (hφ ω.1 ω.2.out).aemeasurable
      {x | angularProjection A x = ω}
    rw [heq, measure_univ] at hm
    exact hm
  · intro E hE
    apply measurable_on_sigma (X := fun j : CuspIndex A =>
      KPCuspCharts.Base F hF (D j).E (D j).integralUnits)
    intro j
    apply measurable_of_countable_open_cover (G j).atlas.baseOpen
      (G j).atlas.open_baseOpen (G j).atlas.cover
    intro i
    let b : (G j).atlas.baseOpen i → KPCuspCharts.Shape F :=
      fun q => ((G j).atlas.baseChart i).symm q |>.val
    have hb : Continuous b :=
      continuous_subtype_val.comp ((G j).atlas.baseChart i).symm.continuous
    have hbq (q : (G j).atlas.baseOpen i) :
        (QuotientAddGroup.mk (b q) : KPCuspCharts.Base F hF (D j).E
          (D j).integralUnits) = q.val := by
      rw [← (G j).atlas.baseChart_formula i (((G j).atlas.baseChart i).symm q)]
      simp
    let ψ : (G j).atlas.baseOpen i × KPCuspCharts.Torus F (D j).L → CrossSection A :=
      fun p => φ j (b p.1) p.2
    have hψ : Measurable ψ := by
      apply Continuous.measurable
      exact (continuous_sigmaMk (σ := fun k : CuspIndex A =>
        KPCuspCharts.CrossQuotient F (KPCuspArithmetic.conjugatedStabilizer F
          (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative k.1))
          ((A.cuspAtlas k.1).cusp k.2) ((A.cuspAtlas k.1).representative k.2)))
        (i := j)).comp ((G j).atlas.continuous_lift.comp
          (continuous_snd.prodMk (hb.comp continuous_fst)))
    have hlocal := measurable_measure_prodMk_left (ν := ν j) (hE.preimage hψ)
    convert hlocal using 1
    funext q
    change K ⟨j,q.val⟩ E = ν j ((fun z => ψ (q,z)) ⁻¹' E)
    rw [← hbq q, hformula, Measure.map_apply (hφ j (b q)) hE]

end DedekindZetaZeroFree.KPMsFixedHaar

end
end

section

noncomputable section
open scoped Classical NumberField ENNReal NNReal
open MeasureTheory

namespace DedekindZetaZeroFree
namespace KPMsFixedHaarDisintegration

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

export KPMsFixedHaar (Cover X archBasepoint SphericalTransport sphericalMeasure
  Radius positiveSlots radialSection RadialData sectionShape radialMeasure
  CuspIndex Parabolic Geometry Omega CrossSection angularProjection logHeight
  AdmissibleCutoff cuspEnds probability kappa AllLevels)

abbrev Disintegration := @KPMsFixedHaar.GeometricDisintegration

theorem actual_haar_normalization
    (μ : Measure (Cover F ζ hζ)) (hμ : μ.IsHaarMeasure) :
    ∃ R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ,
      R.adelicHaar = μ ∧ R.quotientHaar.IsOpenPosMeasure ∧
      Nonempty (SphericalTransport F ζ hζ) := by
  obtain ⟨R, hR, hpos⟩ := KPMsFixedHaar.fixed_haar_recipe F ζ hζ μ hμ
  obtain ⟨P⟩ := KPMsFixedHaar.spherical_transport_exists F ζ hζ
  exact ⟨R, hR, hpos, ⟨P⟩⟩

theorem disintegration_at_fixed_haar
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : SphericalTransport F ζ hζ) : Nonempty (AllLevels F ζ hζ R P) :=
  KPMsFixedHaar.coherent_cusp_geometry F ζ hζ R P
    (fun _ _ A => (KPMsFixedHaar.probability_fiber_kernel A).some)

end KPMsFixedHaarDisintegration

theorem kp_ms_fixed_haar_disintegration
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (μ : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμ : μ.IsHaarMeasure) :
    ∃ R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ,
      R.adelicHaar = μ ∧ R.quotientHaar.IsOpenPosMeasure ∧
      ∃ P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ,
        Nonempty (KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P) := by
  obtain ⟨R, hR, hpos, ⟨P⟩⟩ :=
    KPMsFixedHaarDisintegration.actual_haar_normalization F ζ hζ μ hμ
  exact ⟨R, hR, hpos, P,
    KPMsFixedHaarDisintegration.disintegration_at_fixed_haar F ζ hζ R P⟩

end DedekindZetaZeroFree

end
end
