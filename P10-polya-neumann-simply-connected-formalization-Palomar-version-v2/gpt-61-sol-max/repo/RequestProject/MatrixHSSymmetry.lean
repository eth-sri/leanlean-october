module

public import RequestProject.DiskHardyConormal


public import RequestProject.PlanarTypes

public import RequestProject.MatrixHS

/-! Hermitian square-summable matrices define self-adjoint bounded operators. -/

public section

namespace PolyaNeumann
open scoped InnerProductSpace ComplexConjugate

private theorem matrix_inner_std_left b n :
    ⟪stdBasisZ n, b⟫_ℂ = b n := by
  simp [stdBasisZ_apply, lp.inner_single_left]

private theorem matrix_adjoint_coefficient (A : L2Z →L[ℂ] L2Z) (m n : ℤ) :
    ContinuousLinearMap.adjoint A (stdBasisZ n) m = conj (A (stdBasisZ m) n) := by
  rw [← matrix_inner_std_left, ContinuousLinearMap.adjoint_inner_right,
    common_conormal_inner_single]

private theorem matrix_operator_ext (A B : L2Z →L[ℂ] L2Z)
    (h : ∀ n, A (stdBasisZ n) = B (stdBasisZ n)) : A = B := by
  apply ContinuousLinearMap.ext_on
    ((Submodule.dense_iff_topologicalClosure_eq_top).2 stdBasisZ.dense_span)
  rintro _ ⟨n, rfl⟩
  exact h n

theorem hsMatrixOp_isSelfAdjoint (a : ℤ × ℤ → ℂ)
    ha
    (hs : ∀ m n, a (m,n) = conj (a (n,m))) :
    IsSelfAdjoint (hsMatrixOp a ha) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  apply matrix_operator_ext
  intro n
  apply lp.ext
  funext m
  rw [matrix_adjoint_coefficient]
  simp  [hsMatrixOp_stdBasisZ]
  exact (hs m n).symm

theorem diagOp_isSelfAdjoint w C
    hw (hs : ∀ n, conj (w n) = w n) :
    IsSelfAdjoint (diagOp w C hw) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  apply matrix_operator_ext
  intro n
  apply lp.ext
  funext m
  rw [matrix_adjoint_coefficient]
  simp  [stdBasisZ_apply]
  grind

end PolyaNeumann