module

public import DedekindZetaZeroFree.Theta.Unfolding.TraceNormalizedSourceData

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
open scoped NumberField Classical
namespace DedekindZetaZeroFree.RootDerivatives
open NumberField MeasureTheory
open MomentSources
variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    (R : PrincipalMellin.ActualRecipe S η)

theorem finite_vector_fixed_near_one (q : KPFinitePlace F)
    (M : LocalImageData R q)
    (v : KPRankOneShellRepair.actualCanonicalImageModule F R.A.zeta12 R.A.primitive_zeta12
      q M.inducing M.inducing.polarization M.haar M.haar_integer) :
    ∃ V : Set (q.adicCompletion F)ˣ, IsOpen V ∧ 1 ∈ V ∧ ∀ u ∈ V,
      KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12
        q M.inducing M.inducing.polarization M.haar M.haar_integer
        (KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) u) v = v := by
  obtain ⟨J, hJ⟩ := KPRankOneShellRepair.actualCanonicalImage_smooth F R.A.zeta12
    R.A.primitive_zeta12 q M.inducing M.inducing.polarization M.haar M.haar_integer v
  refine ⟨KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) ⁻¹' J,
    J.isOpen.preimage ((KPPGLLocalCover.finite_lifts_continuous F R.A.zeta12 R.A.primitive_zeta12 q _
      (KPAdelicCoverRestrictedProduct.depth_admissible F R.A.zeta12 R.A.primitive_zeta12 q)).2.2), ?_, fun u hu => hJ _ hu⟩
  change KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) 1 ∈ J
  simp only [KPPGLLocalCover.A, KPStandardLocalRootLifts.A_one, map_one]
  exact J.one_mem

theorem finite_diagonal_constant_near_one (q : KPFinitePlace F)
    (M : LocalImageData R q)
    (ell : KPRankOneShellRepair.actualCanonicalImageModule F R.A.zeta12 R.A.primitive_zeta12
      q M.inducing M.inducing.polarization M.haar M.haar_integer →ₗ[ℂ] ℂ)
    (v : KPRankOneShellRepair.actualCanonicalImageModule F R.A.zeta12 R.A.primitive_zeta12
      q M.inducing M.inducing.polarization M.haar M.haar_integer) :
    ∃ V : Set (q.adicCompletion F)ˣ, IsOpen V ∧ 1 ∈ V ∧ ∀ u ∈ V,
      ell (KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12
        q M.inducing M.inducing.polarization M.haar M.haar_integer
        (KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) u) v) = ell v := by
  obtain ⟨V, hVo, hV1, hfix⟩ := finite_vector_fixed_near_one R q M v
  exact ⟨V, hVo, hV1, fun u hu => congrArg ell (hfix u hu)⟩

theorem factorization_bad_functional_ne_zero
    {Q : AdmissibleFlatSources R} {T : Realization R Q}
    (D : SourceFactorization R Q T) (p : KPHilbert.Place F) (hp : p ∈ D.bad) :
    D.ell p ≠ 0 := by
  obtain ⟨s, x, hs, hx⟩ := D.detected_tensor
  intro hz
  apply (Finset.prod_ne_zero_iff.mp (by
    rw [← D.product_exact s x]
    exact hx)) (⟨p, by rw [hs]; exact hp⟩ : s.val) (Finset.mem_univ _)
  rw [hz]
  rfl

theorem factorization_functional_ne_zero
    {Q : AdmissibleFlatSources R} {T : Realization R Q}
    (D : SourceFactorization R Q T) (p : KPHilbert.Place F) : D.ell p ≠ 0 := by
  by_cases hp : p ∈ D.bad
  · exact factorization_bad_functional_ne_zero R D p hp
  · intro hz
    have hv := D.reference_value p hp
    rw [hz] at hv
    exact zero_ne_one hv

theorem factorization_finite_unit_vector
    {Q : AdmissibleFlatSources R} {T : Realization R Q}
    (D : SourceFactorization R Q T) (q : R.A.Sf) :
    ∃ (v : actualLocal R D.finiteData (Sum.inr q.val))
      (V : Set (q.val.adicCompletion F)ˣ),
      D.ell (Sum.inr q.val) v = 1 ∧ IsOpen V ∧ 1 ∈ V ∧ ∀ u ∈ V,
      D.ell (Sum.inr q.val)
        (KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12
          q.val (D.finiteData q.val).inducing (D.finiteData q.val).inducing.polarization
          (D.finiteData q.val).haar (D.finiteData q.val).haar_integer
          (KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q.val) u) v) = 1 := by
  have hex : ∃ x, D.ell (Sum.inr q.val) x ≠ 0 := by
    by_contra h
    apply (factorization_functional_ne_zero R D (Sum.inr q.val))
    ext x
    simpa using (not_exists.mp h x)
  obtain ⟨x, hx⟩ := hex
  let v := (D.ell (Sum.inr q.val) x)⁻¹ • x
  have hv : D.ell (Sum.inr q.val) v = 1 := by simp [v, hx]
  obtain ⟨V, hVo, hV1, hconst⟩ := finite_diagonal_constant_near_one R q.val
    (D.finiteData q.val) (D.ell (Sum.inr q.val)) v
  exact ⟨v, V, hv, hVo, hV1, fun u hu => (hconst u hu).trans hv⟩

end DedekindZetaZeroFree.RootDerivatives

end
