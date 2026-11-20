module

public import DedekindZetaZeroFree.Adeles.Characters.SIntegerTraceAnnihilation
public import DedekindZetaZeroFree.Adeles.Characters.TraceCharacterNondegeneracy
public import DedekindZetaZeroFree.Adeles.Approximation.FiniteAdeleDensity

@[expose] public section

noncomputable section

open scoped NumberField Classical ENNReal
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.KPAdditiveFundamentalDomain

variable (F : Type) [Field F] [NumberField F]

def archParallelepiped : Set (InfiniteAdeleRing F) :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F) ⁻¹'
    ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)

def domain : Set (AdeleRing (𝓞 F) F) :=
  archParallelepiped F ×ˢ
    (KPAdelicTopology.integralAdeles F : Set (FiniteAdeleRing (𝓞 F) F))

scoped instance principalTranslation : AddAction F (AdeleRing (𝓞 F) F) where
  vadd a x := algebraMap F (AdeleRing (𝓞 F) F) a + x
  zero_vadd x := by
    change algebraMap F (AdeleRing (𝓞 F) F) 0 + x = x
    simp
  add_vadd a b x := by
    change algebraMap F (AdeleRing (𝓞 F) F) (a + b) + x =
      algebraMap F (AdeleRing (𝓞 F) F) a +
        (algebraMap F (AdeleRing (𝓞 F) F) b + x)
    simp [add_assoc]

open scoped DedekindZetaZeroFree.KPAdditiveFundamentalDomain

theorem principalTranslation_apply (a : F) (x : AdeleRing (𝓞 F) F) :
    a +ᵥ x = algebraMap F (AdeleRing (𝓞 F) F) a + x := rfl

 def archHomeo : InfiniteAdeleRing F ≃ₜ mixedEmbedding.mixedSpace F :=
  (Homeomorph.piEquivPiSubtypeProd (fun v : InfinitePlace F => v.IsReal)
    (fun v => v.Completion)).trans
    (Homeomorph.prodCongr
      (Homeomorph.piCongrRight (fun v =>
        (InfinitePlace.Completion.isometryEquivRealOfIsReal v.2).toHomeomorph))
      ((Homeomorph.piCongrRight (fun v =>
        (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
          (InfinitePlace.not_isReal_iff_isComplex.mp v.2)).toHomeomorph)).trans
        (Homeomorph.piCongrLeft (Y := fun _ => ℂ)
          (Equiv.subtypeEquivRight (fun _ => InfinitePlace.not_isReal_iff_isComplex)))))

private theorem archHomeo_apply (x : InfiniteAdeleRing F) :
    archHomeo F x = InfiniteAdeleRing.ringEquiv_mixedSpace F x := rfl

private theorem exists_reduction (a : AdeleRing (𝓞 F) F) :
    ∃ z : F, a - algebraMap F (AdeleRing (𝓞 F) F) z ∈ domain F := by
  let b := mixedEmbedding.latticeBasis F
  let e := archHomeo F
  obtain ⟨r, hrem⟩ := KPAdelicTopology.exists_integral_remainder F a.2
  let y := e (a.1 - algebraMap F (InfiniteAdeleRing F) r)
  obtain ⟨s, hs⟩ := ((mixedEmbedding.mem_span_latticeBasis F).mp (ZSpan.floor b y).property)
  let z := r + (s : F)
  refine ⟨z, ⟨?_, ?_⟩⟩
  · change InfiniteAdeleRing.ringEquiv_mixedSpace F
      (a.1 - algebraMap F (InfiniteAdeleRing F) z) ∈ ZSpan.fundamentalDomain b
    rw [← archHomeo_apply]
    have hmap (x : InfiniteAdeleRing F) (t : F) :
        e (x - algebraMap F (InfiniteAdeleRing F) t) = e x - mixedEmbedding F t := by
      simp only [e, archHomeo_apply, map_sub,
        ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
    have hfrac : e (a.1 - algebraMap F (InfiniteAdeleRing F) z) = ZSpan.fract b y := by
      rw [ZSpan.fract_apply, ← hs]
      change e (a.1 - algebraMap F (InfiniteAdeleRing F) (r + (s : F))) =
        e (a.1 - algebraMap F (InfiniteAdeleRing F) r) - mixedEmbedding F (s : F)
      rw [hmap, hmap, map_add]
      abel
    rw [hfrac]
    exact ZSpan.fract_mem_fundamentalDomain b y
  · dsimp [z]
    rw [map_add, ← sub_sub]
    refine (KPAdelicTopology.integralAdeles F).sub_mem hrem ?_
    exact fun v => HeightOneSpectrum.coe_algebraMap_mem (RingOfIntegers F) F v s

theorem projection_surjective :
    (QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 F) F)) ''
      domain F = Set.univ := by
  apply Set.eq_univ_of_forall
  intro q
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective
    (AdeleRing.principalSubgroup (𝓞 F) F) q
  obtain ⟨z, hz⟩ := exists_reduction F a
  refine ⟨a - algebraMap F (AdeleRing (𝓞 F) F) z, hz, ?_⟩
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  simpa using
    (AdeleRing.principalSubgroup (𝓞 F) F).neg_mem (⟨z, rfl⟩)

theorem projection_injective :
    Set.InjOn (QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 F) F))
      (domain F) := by
  intro x hx y hy hxy
  obtain ⟨c, hc⟩ := (QuotientAddGroup.eq_iff_sub_mem.mp hxy)
  have hfin : algebraMap F (FiniteAdeleRing (𝓞 F) F) c ∈
      KPAdelicTopology.integralAdeles F := by
    have h := (KPAdelicTopology.integralAdeles F).sub_mem hx.2 hy.2
    have heq := congrArg Prod.snd hc
    change algebraMap F (FiniteAdeleRing (𝓞 F) F) c = x.2 - y.2 at heq
    rwa [← heq] at h
  have hfinite : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F c ≤ 1 := by
    intro v
    have hv := hfin v
    change (c : v.adicCompletion F) ∈ v.adicCompletionIntegers F at hv
    simpa only [HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.adicCompletion.valued_coe] using hv
  obtain ⟨s, hs⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F c hfinite
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  have harch : e x.1 - e y.1 = mixedEmbedding F c := by
    have heq := congrArg Prod.fst hc
    change algebraMap F (InfiniteAdeleRing F) c = x.1 - y.1 at heq
    rw [← map_sub, ← heq, ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  have hspan : -e y.1 + e x.1 ∈
      Submodule.span ℤ (Set.range (mixedEmbedding.latticeBasis F)) := by
    rw [add_comm, ← sub_eq_add_neg, harch]
    apply (mixedEmbedding.mem_span_latticeBasis F).mpr
    exact ⟨s, congrArg (mixedEmbedding F) hs⟩
  have harchEq : e y.1 = e x.1 := by
    have h := (ZSpan.fract_eq_fract (mixedEmbedding.latticeBasis F) (e y.1) (e x.1)).mpr hspan
    rw [ZSpan.fract_eq_self.mpr hy.1, ZSpan.fract_eq_self.mpr hx.1] at h
    exact h
  have hc0 : c = 0 := by
    apply mixedEmbedding_injective
    simpa [harchEq] using harch.symm
  have heq : x - y = 0 := by simpa [hc0] using hc.symm
  exact sub_eq_zero.mp heq

theorem compact_closed_cover :
    IsCompact (closure (archParallelepiped F) ×ˢ
      (KPAdelicTopology.integralAdeles F : Set (FiniteAdeleRing (𝓞 F) F))) := by
  refine (((archHomeo F).isCompact_preimage.mpr
    (mixedEmbedding.latticeBasis F).parallelepiped.isCompact).closure_of_subset ?_).prod (KPAdelicTopology.integralAdeles_isCompact F)
  intro x hx
  rw [Set.mem_preimage, archHomeo_apply]
  exact ZSpan.fundamentalDomain_subset_parallelepiped _ hx

theorem quotient_compactSpace :
    CompactSpace (AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F) := by
  let q := QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 F) F)
  have hq : Continuous q := QuotientAddGroup.continuous_mk
  have hC : IsCompact (q '' (closure (archParallelepiped F) ×ˢ
      (KPAdelicTopology.integralAdeles F : Set (FiniteAdeleRing (𝓞 F) F)))) :=
    (compact_closed_cover F).image hq
  apply isCompact_univ_iff.mp
  apply hC.of_isClosed_subset isClosed_univ
  rw [← projection_surjective F]
  apply Set.image_mono
  exact Set.prod_mono subset_closure (Set.Subset.refl _)

theorem domain_measurableSet : MeasurableSet (domain F) := by
  letI : MeasurableSpace (InfiniteAdeleRing F) := borel _
  letI : BorelSpace (InfiniteAdeleRing F) := ⟨rfl⟩
  have hc : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
    rw [← (funext (archHomeo_apply F))]
    exact (archHomeo F).continuous
  have hP :=
    (ZSpan.fundamentalDomain_measurableSet (mixedEmbedding.latticeBasis F)).preimage
      hc.measurable
  have hO := (KPAdelicTopology.integralAdeles_isOpen F).measurableSet
  let AdeleRing₀ := AdeleRing (𝓞 F) F
  have hcfst : Continuous (fun x : AdeleRing₀ => x.1) := continuous_fst
  have hcsnd : Continuous (fun x : AdeleRing₀ => x.2) := continuous_snd
  have hfst : Measurable (fun x : AdeleRing₀ => x.1) := hcfst.measurable
  have hsnd : Measurable (fun x : AdeleRing₀ => x.2) := hcsnd.measurable
  exact (hP.preimage hfst).inter (hO.preimage hsnd)

variable (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]

theorem isAddFundamentalDomain :
    IsAddFundamentalDomain F (domain F) μ := by
  apply IsAddFundamentalDomain.mk' (domain_measurableSet F).nullMeasurableSet
  intro x
  obtain ⟨z, hz⟩ := exists_reduction F x
  have hz' : (-z) +ᵥ x ∈ domain F := by
    simpa only [principalTranslation_apply, map_neg, sub_eq_add_neg, add_comm] using hz
  refine ⟨-z, hz', ?_⟩
  intro w hw
  have hq (a : F) :
      QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 F) F) (a +ᵥ x) =
        QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 F) F) x := by
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    simpa only [principalTranslation_apply, add_sub_cancel_right] using
      (show algebraMap F (AdeleRing (𝓞 F) F) a ∈
        AdeleRing.principalSubgroup (𝓞 F) F from ⟨a, rfl⟩)
  apply (algebraMap F (AdeleRing (𝓞 F) F)).injective
  exact add_right_cancel (projection_injective F hw hz' ((hq w).trans (hq (-z)).symm))

theorem domain_mass :
    0 < μ (domain F) ∧ μ (domain F) < ∞ := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI : VAddInvariantMeasure F (AdeleRing (𝓞 F) F) μ := ⟨fun c s hs => by
    exact measure_preimage_add μ _ s⟩
  refine ⟨pos_iff_ne_zero.mpr ((isAddFundamentalDomain F μ).measure_ne_zero (NeZero.ne μ)), ?_⟩
  letI : IsFiniteMeasureOnCompacts μ := inferInstance
  exact lt_of_le_of_lt
    (measure_mono (Set.prod_mono subset_closure (Set.Subset.refl _)))
    (@IsCompact.measure_lt_top (AdeleRing (𝓞 F) F) _ _ μ _ _ (compact_closed_cover F))

end DedekindZetaZeroFree.KPAdditiveFundamentalDomain

end
