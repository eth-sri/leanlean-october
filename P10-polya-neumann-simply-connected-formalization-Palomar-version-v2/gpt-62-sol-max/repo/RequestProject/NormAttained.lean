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
  obtain ⟨v, hv⟩ := ((hT.hasEigenvalue_iff_mem_spectrum hk0).2 hk).exists_hasEigenvector
  exact ⟨v, hv.2, hv.apply_eq_smul⟩

/-- A nonzero compact normal operator attains its norm at a spectral value. -/
theorem exists_eigenvector_at_norm {T : H →L[ℂ] H} (hT : IsCompactOperator T)
    (hn : IsStarNormal T) (hT0 : T ≠ 0) :
    ∃ k v, k ∈ spectrum ℂ T ∧ k ≠ 0 ∧ ‖k‖ = ‖T‖ ∧ v ≠ 0 ∧ T v = k • v := by
  haveI : Nontrivial H := by
    contrapose! hT0
    exact ContinuousLinearMap.ext fun _ => Subsingleton.elim _ _
  obtain ⟨k, hk, hn'⟩ := spectrum.exists_nnnorm_eq_spectralRadius T
  have hkn := congrArg NNReal.toReal
    (ENNReal.coe_inj.mp (hn'.trans hn.spectralRadius_eq_nnnorm))
  have hk0 : k ≠ 0 := fun h => hT0 (norm_eq_zero.mp (hkn.symm.trans (by simp_all)))
  obtain ⟨v, hv₀, hv⟩ := exists_eigenvector_of_mem_spectrum hT hk hk0
  exact ⟨k, v, hk, hk0, hkn, hv₀, hv⟩

set_option synthInstance.maxHeartbeats 10000000 in
set_option maxHeartbeats 10000000 in
/-- **Lemma 9.2 (norm attained).** If `U` is unitary, `U - I` is compact and `U ≠ I`, then
some eigenvalue `z ≠ 1` of `U` satisfies `|z - 1| = ‖U - I‖`. -/
theorem exists_eigenvalue_norm_sub_one {U : H →L[ℂ] H} (hU : U ∈ unitary (H →L[ℂ] H))
    (hC : IsCompactOperator ⇑(U - 1)) (h1 : U ≠ 1) :
    ∃ (z : ℂ) (v : H), v ≠ 0 ∧ U v = z • v ∧ z ≠ 1 ∧ ‖z - 1‖ = ‖U - 1‖ := by
  letI := isStarNormal_of_mem_unitary hU
  have hn : IsStarNormal (U - 1) := Commute.isStarNormal_sub (by rw [star_one]; exact Commute.one_right U)
  obtain ⟨k, v, _, hk0, hkn, hv0, hv⟩ := exists_eigenvector_at_norm hC hn (sub_ne_zero.mpr h1)
  refine ⟨1 + k, v, hv0, ?_, ?_, ?_⟩
  · rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply] at hv
    rw [add_smul, one_smul, ← hv]; abel
  simp_all
  simp_all

end PolyaNeumann

end
