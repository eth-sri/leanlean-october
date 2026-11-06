module

public import RequestProject.NeumannNormalizedBoundary
public import RequestProject.MatrixHSSymmetry
public import RequestProject.NormalizedPeriodicRegular

/-! Self-adjointness of the actual corrected periodic regular boundary operator. -/

public section

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
  · exact map_zero _
  · exact Complex.conj_ofReal _

theorem correctedRemainderMatrix_zero_hermitian
       
    (hK : LipschitzWith K γ) (hW : IsTransport γ E W) m n :
    correctedRemainderMatrix W 0 0 (m,n) =
      conj (correctedRemainderMatrix W 0 0 (n,m)) := by
  have hc := correctedKernelCoeff_conj_symm hK hW (-n) m
  simp   at hc
  simp only [correctedRemainderMatrix]
  simp only [map_mul, Complex.conj_ofReal]
  congr 1
  ring

end PolyaNeumann