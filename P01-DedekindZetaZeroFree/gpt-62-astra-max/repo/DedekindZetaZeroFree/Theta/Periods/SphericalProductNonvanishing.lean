module

public import DedekindZetaZeroFree.Theta.Whittaker.SphericalFactorizationForms
public import DedekindZetaZeroFree.Eisenstein.Residues.FlatSectionNondegeneracy
public import DedekindZetaZeroFree.Theta.Periods.SphericalTensorResidueData

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
namespace DedekindZetaZeroFree.RootDerivatives
open NumberField MeasureTheory MomentSources FourierContinuation FourierContinuation.ComplexLines
open KPCplxActualImage KPCplxWhittakerUnique
open KPActualReflectionData.StandardLocalSource
open KPReferenceChange.StandardComplexImage
variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

variable {Q : AdmissibleFlatSources R} {T : Realization R Q} (D : SourceFactorization R Q T)

theorem prepared_spherical_period_ne_zero
    (K : PreparedSphericalTensor R D)
    (L : ∀w:InfinitePlace F,Theta frequency →L[ℂ] ℂ)
    (hr : ∀w v,L w (coreInStandardImage v)=D.ell (Sum.inl w) v)
    (hn : ∀w,L w sphericalSeed≠0) :
    fourier R Q.dq K.value 1 ≠ 0 := by
  rw [K.product_at_one]
  apply Finset.prod_ne_zero_iff.mpr
  intro p h_all
  rcases p with ⟨p,hp⟩
  cases p with
  | inl w =>
    rw [K.spherical w hp,←hr,coreInStandardImage_spherical]
    exact hn w
  | inr q =>
    have hq : q∈R.A.Sf := by
      have h := (D.bad_exact (Sum.inr q)).mp (K.stage_exact ▸ hp)
      rcases h with ⟨w,h⟩ | ⟨q0,h,hq0⟩
      · cases h
      · cases h;exact hq0
    rw [K.finite_value ⟨q,hq⟩ hp]
    exact one_ne_zero

include D in
theorem factorization_source_detected :
    ∃v,(Q.flat v).val 0≠0 ∧ T.theta v≠0 ∧ fourier R Q.dq (T.theta v) 1≠0 := by
  obtain ⟨v,hv⟩ := D.detected
  have ht : T.theta v≠0 := by
    intro h
    apply hv
    rw [h]
    simp [MomentSources.fourier]
  refine ⟨v,?_,ht,hv⟩
  exact (realizationScalarResidue T v).zero_section_ne_zero Q.iwasawa ht

theorem prepared_spherical_period_product
    (K : PreparedSphericalTensor R D)
    (L : ∀w:InfinitePlace F,Theta frequency →L[ℂ] ℂ)
    (hr : ∀w v,L w (coreInStandardImage v)=D.ell (Sum.inl w) v) :
    fourier R Q.dq K.value 1 = ∏w,L w sphericalSeed := by
  rw [K.product_at_one]
  have hm (w:InfinitePlace F) : Sum.inl w∈K.stage.val := by
    rw [K.stage_exact]
    exact (D.bad_exact _).mpr (Or.inl ⟨w,rfl⟩)
  symm
  apply Fintype.prod_of_injective (fun w=>⟨Sum.inl w,hm w⟩)
  · intro a b h
    exact Sum.inl_injective (congrArg Subtype.val h)
  · rintro ⟨p,hp⟩ h
    cases p with
    | inl w => exact False.elim (h ⟨w,rfl⟩)
    | inr q =>
      refine K.finite_value ⟨q,?_⟩ hp
      rcases (D.bad_exact _).mp (K.stage_exact ▸ hp) with ⟨w,h⟩|⟨q0,h,hq0⟩
      · cases h
      · cases h;exact hq0
  · intro w
    rw [K.spherical,←hr,coreInStandardImage_spherical]

end DedekindZetaZeroFree.RootDerivatives

end
