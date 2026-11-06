module

public import DedekindZetaZeroFree.Eisenstein.Induction.RestrictedTensorRealization
public import DedekindZetaZeroFree.Metaplectic.Torus.ReferencePeriodization

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators
open NumberField IsDedekindDomain
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.EisensteinReferenceSections.RawSource
open KPAdelicCoverRestrictedProduct KPGlobalTorusFiniteStages
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (P : CompatibleModelData F ζ hζ) (C : LocalFiberData F ζ hζ P)

def archProduct (g : RestrictedCover F ζ hζ) : ℂ :=
  ∏ w, LocalCovariance.arch F ζ hζ w (g (Sum.inl w))

def value (g : RestrictedCover F ζ hζ) :
    KPGlobalTorusPeriodizationInverse.ProductUnitary F ζ hζ P :=
  archProduct F ζ hζ g • SourceTensor.realization F ζ hζ P C
    (SourceTensor.evaluatedTensor F ζ hζ P C g)


















theorem value_scalar (g : RestrictedCover F ζ hζ) (z : Ideles F) :
    value F ζ hζ P C (scalarTuple F ζ hζ z * g) = value F ζ hζ P C g := by
  rw [value, value, SourceTensor.evaluatedTensor_scalar]
  congr 1
  apply Finset.prod_congr rfl
  intro w _
  exact LocalCovariance.arch_scalar F ζ hζ w _ _


















theorem evaluated_central (g : RestrictedCover F ζ hζ) (e : CentralTuples F) :
    SourceTensor.realization F ζ hζ P C
      (SourceTensor.evaluatedTensor F ζ hζ P C (centralTupleMap F ζ hζ e * g)) =
    (∏ᶠ q, (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ (e (Sum.inr q)) : ℂ)) •
      SourceTensor.realization F ζ hζ P C (SourceTensor.evaluatedTensor F ζ hζ P C g) := by
  let t := SourceTensor.evaluatedStage F ζ hζ P C g
  have hefin : {q : HeightOneSpectrum (𝓞 F) | e (Sum.inr q) ≠ 1}.Finite :=
    (centralTuples_finiteSupport F e).preimage Sum.inr_injective.injOn
  let u : RestrictedTensorSimple.Level C.exceptional :=
    ⟨t.val ∪ hefin.toFinset, t.property.trans Finset.subset_union_left⟩
  have htail q (hq : q ∉ u.val) :
      (LocalSeed.finite F ζ hζ P C q).val
        (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (g (Sum.inr q))) =
        localReference F ζ hζ P C q := by
    exact SourceTensor.evaluatedStage_tail F ζ hζ P C g q
      (fun h => hq (Finset.mem_union_left _ h))
  have hetail q (hq : q ∉ u.val) : e (Sum.inr q) = 1 := by
    by_contra h
    exact hq (Finset.mem_union_right _ (hefin.mem_toFinset.mpr h))
  have htail' q (hq : q ∉ u.val) :
      (LocalSeed.finite F ζ hζ P C q).val
        (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
          ((centralTupleMap F ζ hζ e * g) (Sum.inr q))) =
        localReference F ζ hζ P C q := by
    change (LocalSeed.finite F ζ hζ P C q).val
      (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
        (KPLocalCover.centralInjection F ζ hζ (Sum.inr q) (e (Sum.inr q)) * g (Sum.inr q))) = _
    rw [LocalCovariance.finite_central, hetail q hq, map_one, Units.val_one, one_smul]
    exact htail q hq
  rw [SourceTensor.evaluatedTensor_stage F ζ hζ P C _ u htail',
    SourceTensor.evaluatedTensor_stage F ζ hζ P C g u htail,
    SourceTensor.realization_stage, SourceTensor.realization_stage]
  have hv : (fun q : u.val => (LocalSeed.finite F ζ hζ P C q.val).val
      (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q.val)
        ((centralTupleMap F ζ hζ e * g) (Sum.inr q.val)))) =
      fun q : u.val => (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ (e (Sum.inr q.val)) : ℂ) •
        (LocalSeed.finite F ζ hζ P C q.val).val
          (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q.val) (g (Sum.inr q.val))) := by
    funext q
    exact LocalCovariance.finite_central F ζ hζ P C q.val _ _
  rw [hv, MultilinearMap.map_smul_univ, map_smul]
  congr 1
  have hp := Finset.prod_coe_sort u.val
    (fun q => (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ (e (Sum.inr q)) : ℂ))
  refine hp.trans ?_
  symm
  apply finprod_eq_prod_of_mulSupport_subset
  intro q hq
  by_contra h
  exact hq (by dsimp only; rw [hetail q h, map_one, Units.val_one])

theorem finprod_places {f : KPHilbert.Place F → ℂ} (hf : Function.HasFiniteMulSupport f) :
    ∏ᶠ v, f v = (∏ w, f (Sum.inl w)) * ∏ᶠ q, f (Sum.inr q) := by
  have hq : Function.HasFiniteMulSupport (fun q => f (Sum.inr q)) :=
    hf.comp_of_injective Sum.inr_injective
  let S : Finset (KPHilbert.Place F) := Finset.univ.disjSum hq.toFinset
  rw [finprod_eq_prod_of_mulSupport_subset f (s := S)]
  · rw [Finset.prod_disjSum, finprod_eq_prod_of_mulSupport_toFinset_subset _ hq (by exact le_rfl)]
  · intro v hv
    cases v with
    | inl w => simp [S]
    | inr q => simpa [S] using hq.mem_toFinset.mpr hv

theorem value_central (g : RestrictedCover F ζ hζ) (e : CentralTuples F) :
    value F ζ hζ P C (centralTupleMap F ζ hζ e * g) =
      (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ (centralProduct F e) : ℂ) •
        value F ζ hζ P C g := by
  rw [value, value, evaluated_central, smul_smul, smul_smul]
  have ha : archProduct F ζ hζ (centralTupleMap F ζ hζ e * g) =
      (∏ w, (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ (e (Sum.inl w)) : ℂ)) *
        archProduct F ζ hζ g := by
    unfold archProduct
    simp_rw [show ∀ w, ((centralTupleMap F ζ hζ e * g) (Sum.inl w)) =
      KPLocalCover.centralInjection F ζ hζ (Sum.inl w) (e (Sum.inl w)) * g (Sum.inl w) from fun _ => rfl,
      LocalCovariance.arch_central]
    exact Finset.prod_mul_distrib
  rw [ha]
  have hefin : Function.HasFiniteMulSupport
      (fun v => (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ (e v) : ℂ)) :=
    (centralTuples_finiteSupport F e).comp (g := fun x =>
      (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ x : ℂ)) (by simp)
  have hc : (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ (centralProduct F e) : ℂ) =
      (∏ w, (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ (e (Sum.inl w)) : ℂ)) *
        ∏ᶠ q, (KPSourceConvention.ordinaryGenuineCharacter F ζ hζ (e (Sum.inr q)) : ℂ) := by
    change ((KPSourceConvention.ordinaryGenuineCharacter F ζ hζ) (∏ᶠ v, e v) : ℂ) = _
    rw [MonoidHom.map_finprod _ (centralTuples_finiteSupport F e)]
    have hs : Function.HasFiniteMulSupport (fun v =>
        KPSourceConvention.ordinaryGenuineCharacter F ζ hζ (e v)) :=
      (centralTuples_finiteSupport F e).comp
        (g := KPSourceConvention.ordinaryGenuineCharacter F ζ hζ) (map_one _)
    exact (MonoidHom.map_finprod (Units.coeHom ℂ) hs).trans (finprod_places F hefin)
  rw [hc]
  congr 1
  ring

theorem value_amalgamation (g : RestrictedCover F ζ hζ) (m : KPAdelicCoverRestrictedProduct.M F ζ hζ) :
    value F ζ hζ P C (m.val * g) = value F ζ hζ P C g := by
  obtain ⟨e, he, hm⟩ := Subgroup.mem_map.mp m.property
  change centralProduct F e = 1 at he
  rw [← hm, value_central, he, map_one, Units.val_one, one_smul]

 theorem value_amalgamation_eq (g h : RestrictedCover F ζ hζ)
    (he : amalgamation F ζ hζ g = amalgamation F ζ hζ h) :
    value F ζ hζ P C g = value F ζ hζ P C h := by
  have hm : g⁻¹ * h ∈ KPAdelicCoverRestrictedProduct.M F ζ hζ := QuotientGroup.eq.mp he
  have hc := M_central F ζ hζ hm
  have hh : (⟨g⁻¹ * h, hm⟩ : KPAdelicCoverRestrictedProduct.M F ζ hζ).val * g = h := by
    change (g⁻¹ * h) * g = h
    rw [← Subgroup.mem_center_iff.mp hc g, ← mul_assoc, mul_inv_cancel, one_mul]
  have hi := value_amalgamation F ζ hζ P C g ⟨_, hm⟩
  rw [hh] at hi
  exact hi.symm

def amalgamatedValue : CubicGL2Adelic F ζ hζ → KPGlobalTorusPeriodizationInverse.ProductUnitary F ζ hζ P :=
  Quotient.lift (value F ζ hζ P C)
    (fun g h he => value_amalgamation_eq F ζ hζ P C g h (Quotient.sound he))

@[simp] theorem amalgamatedValue_raw (g : RestrictedCover F ζ hζ) :
    amalgamatedValue F ζ hζ P C (amalgamation F ζ hζ g) = value F ζ hζ P C g := rfl

theorem amalgamatedValue_scalar (z : Ideles F) (g : CubicGL2Adelic F ζ hζ) :
    amalgamatedValue F ζ hζ P C (scalarHom F ζ hζ z * g) =
      amalgamatedValue F ζ hζ P C g := by
  induction g using QuotientGroup.induction_on with
  | H g =>
    change amalgamatedValue F ζ hζ P C
      (amalgamation F ζ hζ (scalarTuple F ζ hζ z) * amalgamation F ζ hζ g) = _
    rw [← map_mul, amalgamatedValue_raw]
    change value F ζ hζ P C (scalarTuple F ζ hζ z * g) = value F ζ hζ P C g
    exact value_scalar F ζ hζ P C g z

 theorem amalgamatedValue_quotient_eq (g h : CubicGL2Adelic F ζ hζ)
    (he : scalarQuotient F ζ hζ g = scalarQuotient F ζ hζ h) :
    amalgamatedValue F ζ hζ P C g = amalgamatedValue F ζ hζ P C h := by
  obtain ⟨z, hz⟩ := QuotientGroup.eq.mp he
  have hc := scalarHom_central F ζ hζ (MonoidHom.mem_range.mpr ⟨z, rfl⟩)
  have hh : scalarHom F ζ hζ z * g = h := by
    rw [← Subgroup.mem_center_iff.mp hc g, hz, ← mul_assoc, mul_inv_cancel, one_mul]
  have hi := amalgamatedValue_scalar F ζ hζ P C z g
  rw [hh] at hi
  exact hi.symm

def quotientValue : KPGlobalTorusFunctionData.G F ζ hζ →
    KPGlobalTorusPeriodizationInverse.ProductUnitary F ζ hζ P :=
  Quotient.lift (amalgamatedValue F ζ hζ P C)
    (fun g h he => amalgamatedValue_quotient_eq F ζ hζ P C g h (Quotient.sound he))

























































def scalarValue (g : KPGlobalTorusFunctionData.G F ζ hζ) : ℂ :=
  (KPGlobalTorusPeriodizationInverse.unitaryPeriodization F ζ hζ P
    (quotientValue F ζ hζ P C g)).val.val 1















































end DedekindZetaZeroFree.EisensteinReferenceSections.RawSource

end
