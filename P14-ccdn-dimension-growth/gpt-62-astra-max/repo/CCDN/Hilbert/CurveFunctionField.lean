/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.FilteredIntersection
public import Mathlib.RingTheory.Algebraic.Defs
import CCDN.Hilbert.FunctionFieldRank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.RingTheory.Localization.Integer

/-! A fraction field of an affine curve is finite over the field of a
transcendental linear parameter, of degree at most its affine Hilbert degree.
Common denominators transfer arbitrary field elements to polynomial classes. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- Multiplying a linearly independent family in a field by a common nonzero element keeps it
linearly independent. -/
lemma field_common_multiple_independent {R F ι : Type*} [Field R] [Field F]
    [Algebra R F] [Fintype ι] [DecidableEq ι]
    (v : ι → F) (hv : LinearIndependent R v) (b : F) (hb : b ≠ 0) :
    LinearIndependent R (fun i => b * v i) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hz : ∑ j, c j • v j = 0 := by
    apply mul_left_cancel₀ hb
    rw [mul_zero, Finset.mul_sum]
    simpa using hc
  exact Fintype.linearIndependent_iff.mp hv c hz i

variable {K R F σ : Type*} [Field K] [Field R] [Field F]
  [Algebra K R] [Algebra R F] [Algebra K F] [IsScalarTower K R F] [Fintype σ]
  (I : Ideal (MvPolynomial σ K)) [I.IsPrime]
  [Algebra (MvPolynomial σ K ⧸ I) F] [IsScalarTower K (MvPolynomial σ K ⧸ I) F]
  [IsFractionRing (MvPolynomial σ K ⧸ I) F]

end
end CCDN
