module

public import DedekindZetaZeroFree.Eisenstein.Induction.TorusTensorFormula
public import DedekindZetaZeroFree.Metaplectic.Torus.PeriodizationAndAveraging

@[expose] public section

noncomputable section
open scoped Classical NumberField NNReal BigOperators
open NumberField IsDedekindDomain
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.EisensteinReferenceSections.ReferencePeriodization
open KPGlobalProductPolarizationCharacter KPAdelicCoverRestrictedProduct
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (P : KPGlobalTorusFiniteStages.CompatibleModelData F ζ hζ)
    (C : KPGlobalTorusFiniteStages.LocalFiberData F ζ hζ P)

theorem local_class_of_raw (raw : RestrictedCover F ζ hζ)
    (e : KPGlobalTorusFunctionData.E F ζ hζ)
    (he : scalarQuotient F ζ hζ (amalgamation F ζ hζ raw) = e.val)
    (v : KPHilbert.Place F) (b : localTorus F ζ hζ v)
    (hb : b.val = KPPGLLocalCover.coverQuotient F ζ hζ v (raw v)) :
    localProjection F ζ hζ v b = KPGlobalCubicIdelePairing.classComparison F
      (pD F ζ hζ e) v := by apply @DedekindZetaZeroFree.KPGlobalTorusFiniteStagesIdentification.CompactTailSupportAndFactorization.raw_local_projection_eq <;> assumption

theorem reference_local_mem (q : HeightOneSpectrum (𝓞 F))
    (t : KPLocalExceptionalConstruction.actualTorus F ζ hζ q)
    (ht : KPGlobalTorusFiniteStages.localUntwistedEvaluation F ζ hζ P C q
      (KPGlobalTorusFiniteStages.localReference F ζ hζ P C q) t ≠ 0) :
    t.val ∈ (localPreimage F ζ hζ (Sum.inr q)
      (P.localData.localData (Sum.inr q)).L).map
        (localTorus F ζ hζ (Sum.inr q)).subtype := by
  have hm : (C.canonical q).heisenberg.π t ∈ (C.polarization q).L := by
    by_contra hm
    apply ht
    simp [KPGlobalTorusFiniteStages.localUntwistedEvaluation,
      KPGlobalTorusFiniteStages.localReference, hm]
  rw [← C.subgroup_matches q]
  exact Subgroup.mem_map.mpr ⟨t, hm, rfl⟩

theorem finiteReference_support (T : Finset (HeightOneSpectrum (𝓞 F)))
    (hT : C.exceptional ⊆ T) (e : KPGlobalTorusFunctionData.E F ζ hζ)
    (hne : (TorusReference.finiteReference F ζ hζ P C T hT).val.val e ≠ 0) :
    e ∈ B F ζ hζ P.localData := by
  obtain ⟨raw, he⟩ := ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)) e.val
  have hd := FullTorusFormula.raw_diagonal F ζ hζ e raw he
  let t (q : HeightOneSpectrum (𝓞 F)) : KPLocalExceptionalConstruction.actualTorus F ζ hζ q :=
    ⟨KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (raw (Sum.inr q)), ⟨(raw (Sum.inr q)).g, rfl, (hd (Sum.inr q)).1, (hd (Sum.inr q)).2⟩⟩
  have hf := FullTorusFormula.finiteTensorRealization_full_raw_formula F ζ hζ P C T hT
    (fun q => KPGlobalTorusFiniteStages.localReference F ζ hζ P C q.val) raw t e
    (fun _ => rfl) he
  change (TorusReference.finiteReference F ζ hζ P C T hT).val.val e = _ at hf
  simp only [dite_eq_ite, ite_self] at hf
  have hs := KPGlobalTorusFiniteStages.local_evaluation_finiteSupport F ζ hζ P C T hT
    (fun q => KPGlobalTorusFiniteStages.localReference F ζ hζ P C q.val) raw t (fun _ => rfl)
  simp only [dite_eq_ite, ite_self] at hs
  intro v
  cases v with
  | inl w => rw [P.localData.complex_full]; trivial
  | inr q =>
    obtain ⟨b, hb, heq⟩ := reference_local_mem F ζ hζ P C q (t q) (fun hz => (fun hh => hne (by rw [hf, hh, mul_zero])) (finprod_eq_zero _ q hz hs))
    rw [← local_class_of_raw F ζ hζ raw e he (Sum.inr q) b heq]
    exact hb

open KPGlobalTorusPeriodizationInverse

theorem reference_periodization_one (T : Finset (HeightOneSpectrum (𝓞 F)))
    (hT : C.exceptional ⊆ T) :
    (unitaryPeriodization F ζ hζ P
      (TorusReference.finiteReference F ζ hζ P C T hT)).val.val 1 = 1 := by
  let s := (rational_representatives_exist F ζ hζ P).choose
  let f := TorusReference.finiteReference F ζ hζ P C T hT
  rw [unitaryPeriodization_formula F ζ hζ P s f 1]
  simp only [mul_one]
  have memB (a : PeriodizationIndex F ζ hζ P) (ha : a = 1) :
      (s.lift a).val ∈ B F ζ hζ P.localData := by
    subst a
    exact ((QuotientGroup.eq_one_iff _).mp (s.projects 1)).2
  have hzero : ∀ a : PeriodizationIndex F ζ hζ P, a ≠ 1 →
      (((KPGlobalTorusFiniteStages.rationalUnitCharacter F ζ hζ (s.lift a))⁻¹ : ℂˣ) : ℂ) *
        f.val.val (s.lift a).val = 0 := by
    intro a ha
    suffices hf : f.val.val (s.lift a).val = 0 by rw [hf, mul_zero]
    by_contra hf
    apply ha
    rw [← s.projects a]
    apply (QuotientGroup.eq_one_iff _).mpr
    exact ⟨(rationalClass F ζ hζ (s.lift a)).property, (finiteReference_support F ζ hζ P C T hT (s.lift a).val hf)⟩
  rw [tsum_eq_single (1 : PeriodizationIndex F ζ hζ P) (fun a ha => hzero a ha)]
  let b : B F ζ hζ P.localData := ⟨(s.lift 1).val, memB 1 rfl⟩
  have hc : KPGlobalTorusFiniteStages.productUnitCharacter F ζ hζ P.localData P.adjustment b =
      KPGlobalTorusFiniteStages.rationalUnitCharacter F ζ hζ (s.lift 1) := by
    change lambdaB F ζ hζ P.localData P.adjustment b /
        KPGlobalCenterRationalCharacter.positiveComplex
          (KPGlobalCenterRationalCharacter.nu F ζ hζ b.val) =
      KPGlobalCenterRationalCharacter.lambdaR F ζ hζ (s.lift 1) /
        KPGlobalCenterRationalCharacter.positiveComplex
          (KPGlobalCenterRationalCharacter.nu F ζ hζ (s.lift 1).val)
    rw [P.agrees b (s.lift 1) rfl]
  have hv := f.val.property b 1
  change f.val.val (b.val * 1) =
    (KPGlobalTorusFiniteStages.productUnitCharacter F ζ hζ P.localData P.adjustment b : ℂ) *
      f.val.val 1 at hv
  rw [mul_one, TorusReference.finiteReference_one F ζ hζ P C T hT, mul_one, hc] at hv
  rw [show f.val.val (s.lift 1).val = _ from hv]
  simp

end DedekindZetaZeroFree.EisensteinReferenceSections.ReferencePeriodization

end
