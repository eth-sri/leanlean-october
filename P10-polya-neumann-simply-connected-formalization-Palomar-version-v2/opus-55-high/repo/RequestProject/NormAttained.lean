module

public import RequestProject.FiniteRankCompletion
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.Spectrum

/-!
# Lemma 9.2: the norm of `U - I` is attained at an eigenvalue

If `U` is a unitary operator on a complex Hilbert space and `U - I` is compact, then
`U - I` is a normal compact operator, so its norm equals its spectral radius, and every nonzero
spectral value of `U - I` is an eigenvalue (Fredholm alternative). Hence, if `U ≠ I`, some
eigenvalue `z ≠ 1` of `U` satisfies `|z - 1| = ‖U - I‖`.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

set_option maxHeartbeats 10000000

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A nonzero spectral value of a compact operator is an eigenvalue (Fredholm alternative). -/
theorem exists_eigenvector_of_mem_spectrum {T : H →L[ℂ] H} (hT : IsCompactOperator T) {k : ℂ}
    (hk : k ∈ spectrum ℂ T) (hk0 : k ≠ 0) : ∃ v : H, v ≠ 0 ∧ T v = k • v := by
  set C : H →L[ℂ] H := (-k⁻¹) • T with hCdef
  have hrel : algebraMap ℂ (H →L[ℂ] H) k - T = k • (1 + C) := by
    rw [smul_add, smul_smul, mul_neg, mul_inv_cancel₀ hk0, neg_one_smul,
      Algebra.algebraMap_eq_smul_one, sub_eq_add_neg]
  by_contra hno
  have hinj : Function.Injective ⇑(1 + C) := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have h2 : k • (v + (-k⁻¹) • T v) = 0 := by simp_all
    rw [smul_add, smul_smul, mul_neg, mul_inv_cancel₀ hk0, neg_one_smul] at h2
    grind
  apply hk
  show IsUnit _
  rw [hrel]
  exact ((IsUnit.mk0 k hk0).map (algebraMap ℂ (H →L[ℂ] H))).mul (isUnit_of_bijective _ ⟨hinj, (injective_iff_surjective_one_add (hT.smul _)).mp hinj⟩)

set_option synthInstance.maxHeartbeats 10000000 in
set_option maxHeartbeats 10000000 in
/-- **Lemma 9.2 (norm attained).** If `U` is unitary, `U - I` is compact and `U ≠ I`, then
some eigenvalue `z ≠ 1` of `U` satisfies `|z - 1| = ‖U - I‖`. -/
theorem exists_eigenvalue_norm_sub_one {U : H →L[ℂ] H} (hU : U ∈ unitary (H →L[ℂ] H))
    (hC : IsCompactOperator ⇑(U - 1)) (h1 : U ≠ 1) :
    ∃ (z : ℂ) (v : H), v ≠ 0 ∧ U v = z • v ∧ z ≠ 1 ∧ ‖z - 1‖ = ‖U - 1‖ := by
  haveI : Nontrivial H := by
    by_contra hH
    rw [not_nontrivial_iff_subsingleton] at hH
    exact h1 (ContinuousLinearMap.ext fun x => Subsingleton.elim _ _)
  obtain ⟨k, hk, hkn⟩ :=
    spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty (spectrum.nonempty (U - 1))
  rw [@IsStarNormal.spectralRadius_eq_nnnorm (H →L[ℂ] H)
      inferInstance (U - 1) (by
    constructor
    rw [Commute, SemiconjBy, star_sub, star_one]
    simp only [sub_mul, mul_sub, Unitary.star_mul_self_of_mem hU, Unitary.mul_star_self_of_mem hU, one_mul, mul_one]
    abel)] at hkn
  have hknNN  := ENNReal.coe_inj.mp hkn
  have hkn' : ‖k‖ = ‖U - 1‖ := by
    linarith
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [norm_zero, eq_comm, norm_eq_zero, sub_eq_zero] at hkn'
    trivial
  obtain ⟨v, hv0, hv⟩ := exists_eigenvector_of_mem_spectrum hC hk hk0
  refine ⟨1 + k, v, hv0, ?_, ?_, ?_⟩
  all_goals simp_all [add_smul, ← hv]

end PolyaNeumann

end
