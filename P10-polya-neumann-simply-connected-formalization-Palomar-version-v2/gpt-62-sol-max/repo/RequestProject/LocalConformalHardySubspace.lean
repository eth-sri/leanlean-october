module

public import RequestProject.HardyAntiderivative
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# The full closed nonpositive Fourier space

The original Hardy input space contains frequency zero. It is precisely
the kernel of the strict-positive Fourier projection; its actual Hilbert
orthogonal projection is therefore identity minus that projection.
These facts prepare the physical fixed-complement chart, without
asserting its still separately required reference-energy injectivity.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open scoped InnerProductSpace

/-- The full nonpositive Fourier input space, including frequency zero. -/
def nonpositiveFourierSubspace : Submodule ℂ L2Z where
  carrier := {b | IsNonpositiveFourierSupport b}
  zero_mem' := by tauto
  add_mem' := by
    intro b d hb hd n hn
    simp [hb n hn, hd n hn]
  smul_mem' := by
    intro c b hb n hn
    simp [hb n hn]

theorem nonpositiveFourierSubspace_eq_ker_posProj :
    nonpositiveFourierSubspace = posProj.ker := by
  apply Submodule.ext
  intro b
  change IsNonpositiveFourierSupport b ↔ posProj b = 0
  constructor
  · intro hb
    apply lp.ext
    funext n
    by_cases hn : 0 < n
    · simp [posProj, hn, hb n hn]
    · simp [posProj, hn]
  · intro hb n hn
    have h := congrArg (fun v : L2Z => v n) hb
    simpa [posProj, diagOp_apply, hn] using h

theorem isClosed_nonpositiveFourierSubspace :
    IsClosed (nonpositiveFourierSubspace : Set L2Z) := by
  rw [nonpositiveFourierSubspace_eq_ker_posProj]
  exact posProj.isClosed_ker

instance nonpositiveFourierSubspaceCompleteSpace :
    CompleteSpace nonpositiveFourierSubspace :=
  isClosed_nonpositiveFourierSubspace.completeSpace_coe

instance nonpositiveFourierComplementCompleteSpace :
    CompleteSpace nonpositiveFourierSubspaceᗮ :=
  nonpositiveFourierSubspace.isClosed_orthogonal.completeSpace_coe

theorem one_sub_posProj_mem_nonpositive (b : L2Z) :
    (1 - posProj) b ∈ nonpositiveFourierSubspace := by
  intro n hn
  simp [ContinuousLinearMap.one_apply,
    posProj, diagOp_apply, hn]

theorem posProj_mem_nonpositive_orthogonal (b : L2Z) :
    posProj b ∈ nonpositiveFourierSubspaceᗮ := by
  rw [Submodule.mem_orthogonal]
  intro a ha
  change IsNonpositiveFourierSupport a at ha
  rw [lp.inner_eq_tsum]
  have hterms : (fun n => ⟪a n, posProj b n⟫_ℂ) = fun _ => (0 : ℂ) := by
    funext n
    by_cases hn : 0 < n
    aesop
    simp_all [posProj, diagOp_apply, hn]
  rw [hterms]
  exact tsum_zero

/-- The zero frequency belongs to the first summand of the actual
orthogonal decomposition used by the physical chart. -/
theorem nonpositiveFourierSubspace_starProjection :
    nonpositiveFourierSubspace.starProjection = 1 - posProj := by
  ext1 b
  apply nonpositiveFourierSubspace.eq_starProjection_of_mem_orthogonal
    (one_sub_posProj_mem_nonpositive b)
  have heq : b - (1 - posProj) b = posProj b := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
    abel
  rw [heq]
  exact posProj_mem_nonpositive_orthogonal b

theorem posProj_stdBasisZ (n : ℤ) :
    posProj (stdBasisZ n) = if 0 < n then stdBasisZ n else 0 := by
  rw [posProj, diagOp_stdBasisZ]
  by_cases hn : 0 < n <;> simp [stdBasisZ_apply, hn]

theorem stdBasisZ_mem_nonpositive {n : ℤ} (hn : n ≤ 0) :
    stdBasisZ n ∈ nonpositiveFourierSubspace := by
  rw [nonpositiveFourierSubspace_eq_ker_posProj]
  change posProj (stdBasisZ n) = 0
  simp [posProj_stdBasisZ, hn.not_gt]

theorem stdBasisZ_isSobolevSeq (s : ℝ) (n : ℤ) : IsSobolevSeq s (stdBasisZ n : ℤ → ℂ) := by
  refine summable_of_ne_finset_zero (s := {n}) fun k hk => ?_
  have hkn : k ≠ n := by simpa using hk
  simp [stdBasisZ_apply, lp.single_apply, hkn]

/-- A bounded operator on Fourier sequences vanishes on the closed nonpositive
subspace if it vanishes on each nonpositive mode. -/
theorem eq_zero_of_nonpositive_modes {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (A : L2Z →L[ℂ] V) (h : ∀ n ≤ 0, A (stdBasisZ n) = 0)
    {b : L2Z} (hb : b ∈ nonpositiveFourierSubspace) : A b = 0 := by
  have hzero : A.comp (1 - posProj) = 0 := by
    apply ContinuousLinearMap.ext_on
      ((Submodule.dense_iff_topologicalClosure_eq_top).2 stdBasisZ.dense_span)
    rintro _ ⟨n, rfl⟩
    by_cases hn : 0 < n
    · simp [posProj_stdBasisZ, hn]
    · simpa [posProj_stdBasisZ, hn] using h n (le_of_not_gt hn)
  rw [nonpositiveFourierSubspace_eq_ker_posProj] at hb
  change posProj b = 0 at hb
  simpa [hb] using DFunLike.congr_fun hzero b

end PolyaNeumann

end
