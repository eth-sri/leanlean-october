
import GS.UnitaryLocalModel.PauliCoordinates
import Mathlib.Analysis.Matrix.Order



/-!
# Uniqueness of positive polar factors

The compact local-model argument needs algebraic uniqueness, rather than a
continuous choice of singular vectors or a constructed matrix polar function.
A positive polar factor is determined by its square; the remaining unitary
factor is then determined by invertibility. The statement is proved in every
finite size and specialized positivity includes the two-by-two anchor blocks.
-/
open Matrix
open scoped ComplexOrder MatrixOrder
namespace GS.UnitaryLocalModel

/-- Equal unitary-times-positive products have equal factors. -/
theorem positive_polar_unique {n : ℕ} (U V P Q : CMat n)
    (hU : GS.Unitary U) (hV : GS.Unitary V)
    (hP : P.PosDef) (hQ : Q.PosDef) (he : U*P = V*Q) :
    U = V ∧ P = Q := by
  have hs : P^2 = Q^2 := by
    have h := congrArg (fun T : CMat n => Tᴴ*T) he
    simpa only [Matrix.conjTranspose_mul, hP.isHermitian.eq, hQ.isHermitian.eq,
      Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, ← Matrix.mul_assoc Vᴴ V,
      hU.1, hV.1, Matrix.one_mul, pow_two] using h
  have hPQ := (CFC.sq_eq_sq_iff P Q hP.posSemidef.nonneg hQ.posSemidef.nonneg).mp hs
  refine ⟨?_, hPQ⟩
  subst Q
  exact hP.isUnit.mul_right_cancel he



end GS.UnitaryLocalModel
