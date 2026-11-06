module
public import GuthMaynard.Improvement.OperatorFiniteCompression
import WeylPort.Analytic.RealLaplace

@[expose] public section
noncomputable section
open MeasureTheory InnerProductSpace
open scoped InnerProductSpace
namespace GuthMaynard.Improvement
variable {E ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Lift a finite-subspace operator to the actual ambient Hilbert space. -/
def operatorSubspaceLift (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    (A : U →L[ℂ] U) : E →L[ℂ] E := U.subtypeL ∘L A ∘L U.orthogonalProjectionOnto

/-- Actual compression acting on the finite subspace. -/
def operatorSubspaceCompression (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    (T : E →L[ℂ] E) : U →L[ℂ] U := U.orthogonalProjectionOnto ∘L T ∘L U.subtypeL

/-- A lift is literally a finite rank-one sum, with the right domain projection. -/
theorem operator_subspace_lift_eq_sum (U : Submodule ℂ E) [U.HasOrthogonalProjection]
    [Fintype κ] (e : OrthonormalBasis κ ℂ U) (A : U →L[ℂ] U) :
    operatorSubspaceLift U A = ∑ j, rankOne ℂ (A (e j) : E) (e j : E) := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [operatorSubspaceLift, ContinuousLinearMap.comp_apply,
    e.orthogonalProjectionOnto_apply_eq_sum, map_sum, map_smul, sum_apply, rankOne_apply]
  rfl

/-- Ambient Hilbert-basis trace equals the finite-dimensional diagonal sum. -/
theorem operator_subspace_lift_trace (b : HilbertBasis ι ℂ E)
    (U : Submodule ℂ E) [U.HasOrthogonalProjection] [Fintype κ]
    (e : OrthonormalBasis κ ℂ U) (A : U →L[ℂ] U) :
    operatorDiagonalTrace b (operatorSubspaceLift U A) =
      ∑ j, inner ℂ (e j) (A (e j)) := by
  rw [operator_subspace_lift_eq_sum U e A]
  have hh := hasSum_sum (s := Finset.univ)
    (fun j _ => operator_rankOne_hasSum b (A (e j) : E) (e j : E))
  pm_99 operatorDiagonalTrace sum_apply inner_sum Submodule.coe_inner hh.tsum_eq

section
variable (U : Submodule ℂ E) [U.HasOrthogonalProjection]
include U
/-- Multiplication of lifted operators agrees exactly with finite multiplication. -/
theorem operator_subspace_lift_mul
    (A B : U →L[ℂ] U) :
    operatorSubspaceLift U (A*B) = operatorSubspaceLift U A * operatorSubspaceLift U B := by
  apply ContinuousLinearMap.ext
  intro v
  pm_503 operatorSubspaceLift ContinuousLinearMap.comp_apply mul_apply_eq_comp Submodule.subtypeL_apply Submodule.orthogonalProjectionOnto_mem_subspace_eq_self

/-- A lifted compressed operator is the literal ambient sandwich PTP. -/
theorem operator_subspace_lift_compression
    (T : E →L[ℂ] E) :
    operatorSubspaceLift U (operatorSubspaceCompression U T) = U.starProjection*T*U.starProjection := by
  rfl
end

section
variable (b : HilbertBasis ι ℂ E) (U : Submodule ℂ E) [U.HasOrthogonalProjection] [Fintype κ] (e : OrthonormalBasis κ ℂ U)
include b U e
/-- Cubic ambient trace is the finite cubic trace, in any finite orthonormal basis. -/
theorem operator_subspace_cubic_trace (T : E →L[ℂ] E) :
    operatorDiagonalTrace b ((U.starProjection*T*U.starProjection)^3) =
      ∑ j, inner ℂ (e j) (((operatorSubspaceCompression U T)^3) (e j)) := by
  rw [← operator_subspace_lift_compression U T]
  have he (A : U →L[ℂ] U) : (operatorSubspaceLift U A)^3 = operatorSubspaceLift U (A^3) := by
    simp only [pow_succ _ 2, pow_two, operator_subspace_lift_mul]
  rw [he, operator_subspace_lift_trace b U e]

/-- Mixed ambient trace is the finite mixed trace; positivity/commutation are unnecessary. -/
theorem operator_subspace_mixed_trace (C H : E →L[ℂ] E) :
    operatorDiagonalTrace b ((U.starProjection*C*U.starProjection)*(U.starProjection*H*U.starProjection)^2) =
      ∑ j, inner ℂ (e j) ((operatorSubspaceCompression U C*(operatorSubspaceCompression U H)^2) (e j)) := by
  rw [← operator_subspace_lift_compression U C, ← operator_subspace_lift_compression U H]
  simp only [pow_two, ← operator_subspace_lift_mul]
  exact operator_subspace_lift_trace b U e _
end

section
variable (U : Submodule ℂ E) [U.HasOrthogonalProjection]
include U
/-- Positivity of the actual compression follows from positivity upstairs. -/
theorem operator_subspace_compression_positive
    {T : E →L[ℂ] E} (hT : T.IsPositive) : (operatorSubspaceCompression U T).IsPositive :=
  hT.orthogonalProjectionOnto_comp U

/-- Compression preserves subtraction exactly. -/
theorem operator_subspace_compression_sub
    (G C : E →L[ℂ] E) : operatorSubspaceCompression U (G-C) =
      operatorSubspaceCompression U G - operatorSubspaceCompression U C := by
  apply ContinuousLinearMap.ext
  intro v
  simp [operatorSubspaceCompression]

/-- Quadratic forms on witnesses lying in U are unchanged by compression. -/
theorem operator_subspace_compression_pairing
    (T : E →L[ℂ] E) (v w : U) :
    inner ℂ v (operatorSubspaceCompression U T w) = inner ℂ (v : E) (T (w : E)) := by
  simp [operatorSubspaceCompression]

/-- The compressed correction inherits the ambient norm bound. -/
theorem operator_subspace_compression_norm
    (T : E →L[ℂ] E) : ‖operatorSubspaceCompression U T‖ ≤ ‖T‖ := by
  apply (operatorSubspaceCompression U T).opNorm_le_bound (norm_nonneg _)
  intro v
  exact (U.norm_orthogonalProjectionOnto_apply_le _).trans (T.le_opNorm (v:E))
end

end GuthMaynard.Improvement
