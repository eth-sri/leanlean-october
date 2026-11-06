module

public import GS.UnitaryLocalModel.PauliCoordinates
public import Mathlib.Analysis.Matrix.Order

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Uniqueness of positive polar factors

The compact local-model argument needs algebraic uniqueness, rather than a
continuous choice of singular vectors or a constructed matrix polar function.
A positive polar factor is determined by its square; the remaining unitary
factor is then determined by invertibility. The statement is proved in every
finite size and specialized positivity includes the two-by-two anchor blocks.
-/
noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder
namespace GS.UnitaryLocalModel
open GS.UnitaryNonmanifold

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
  have hPQ : P = Q := (CFC.sq_eq_sq_iff P Q hP.posSemidef.nonneg hQ.posSemidef.nonneg).mp hs
  refine ⟨?_, hPQ⟩
  subst Q
  exact hP.isUnit.mul_right_cancel he

/-- The right-positive convention has the same uniqueness property. -/
theorem positive_polar_unique_right {n : ℕ} (U V P Q : CMat n)
    (hU : GS.Unitary U) (hV : GS.Unitary V)
    (hP : P.PosDef) (hQ : Q.PosDef) (he : P*U = Q*V) :
    U = V ∧ P = Q := by
  have ht : Uᴴ*P = Vᴴ*Q := by
    simpa only [Matrix.conjTranspose_mul, hP.isHermitian.eq, hQ.isHermitian.eq]
      using congrArg Matrix.conjTranspose he
  obtain ⟨hUV, hPQ⟩ := positive_polar_unique Uᴴ Vᴴ P Q
    hU.conjTranspose hV.conjTranspose hP hQ ht
  exact ⟨Matrix.conjTranspose_injective hUV, hPQ⟩

end GS.UnitaryLocalModel
