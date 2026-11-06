module

public import RequestProject.NeumannRegularSelfAdjoint
public import RequestProject.MatrixHSSymmetry
public import RequestProject.NormalizedPeriodicRegular

/-! Self-adjointness of the actual corrected periodic regular boundary operator. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PolyaNeumann
open Real
open scoped ComplexConjugate

theorem normalizedInverseAbsOperator_isSelfAdjoint :
    IsSelfAdjoint normalizedInverseAbsOperator := by
  apply diagOp_isSelfAdjoint
  intro n
  unfold normalizedInverseAbsSymbol
  split_ifs <;> simp

theorem principalNormalized_isSelfAdjoint : IsSelfAdjoint principalNormalized := by
  apply diagOp_isSelfAdjoint
  intro n
  unfold principalSymbol
  split_ifs
  · norm_num
  · exact Complex.conj_ofReal _

theorem correctedRemainderMatrix_zero_hermitian
    {γ : ℝ → ℂ} {K : NNReal} {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hK : LipschitzWith K γ) (hW : IsTransport γ E W) (m n : ℤ) :
    correctedRemainderMatrix W 0 0 (m,n) =
      conj (correctedRemainderMatrix W 0 0 (n,m)) := by
  simp only [correctedRemainderMatrix]
  rw [correctedKernelCoeff_conj_symm hK hW (-n) m]
  simp only [map_mul, Complex.conj_ofReal]
  ring

end PolyaNeumann
end
