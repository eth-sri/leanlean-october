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
  obtain ⟨v, hv, hv₀⟩ := ((hT.hasEigenvalue_iff_mem_spectrum hk0).mpr hk).exists_hasEigenvector
  exact ⟨v, hv₀, Module.End.mem_eigenspace_iff.mp hv⟩

set_option synthInstance.maxHeartbeats 10000000 in
set_option maxHeartbeats 10000000 in
/-- **Lemma 9.2 (norm attained).** If `U` is unitary, `U - I` is compact and `U ≠ I`, then
some eigenvalue `z ≠ 1` of `U` satisfies `|z - 1| = ‖U - I‖`. -/
theorem exists_eigenvalue_norm_sub_one {U : H →L[ℂ] H} (hU : U ∈ unitary (H →L[ℂ] H))
    (hC : IsCompactOperator ⇑(U - 1)) (h1 : U ≠ 1) :
    ∃ (z : ℂ) (v : H), v ≠ 0 ∧ U v = z • v ∧ z ≠ 1 ∧ ‖z - 1‖ = ‖U - 1‖ := by
  have hn : IsStarNormal (U - 1) := by
    constructor
    rw [Commute, SemiconjBy, star_sub, star_one]
    have h1 := Unitary.star_mul_self_of_mem hU
    have h2 := Unitary.mul_star_self_of_mem hU
    simp [sub_mul, mul_sub, h1, h2]
    abel
  letI  := hn
  haveI : Nontrivial H := by
    by_contra hH
    rw [not_nontrivial_iff_subsingleton] at hH
    exact h1 (ContinuousLinearMap.ext fun x => Subsingleton.elim _ _)
  obtain ⟨k, hk, hkn⟩ :=
    spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty (spectrum.nonempty (U - 1))
  have hspec  :=
    @IsStarNormal.spectralRadius_eq_nnnorm (H →L[ℂ] H)
      inferInstance (U - 1) hn
  rw [hspec] at hkn
  have hknNN := ENNReal.coe_inj.mp hkn
  have hkn' : ‖k‖ = ‖U - 1‖ := by
    simpa using congrArg NNReal.toReal hknNN
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [norm_zero, eq_comm, norm_eq_zero, sub_eq_zero] at hkn'
    exact h1 hkn'
  obtain ⟨v, hv0, hv⟩ := exists_eigenvector_of_mem_spectrum hC hk hk0
  refine ⟨1 + k, v, hv0, ?_, ?_, ?_⟩
  · rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply] at hv
    rw [add_smul, one_smul, ← hv]; abel
  · simp [*]
  · simp [*]

end PolyaNeumann

end
