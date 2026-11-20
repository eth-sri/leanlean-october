module

public import QPBT.Test.MagicSquareTheorems.Rigidity.Transfer
public import QPBT.Test.MagicSquareTheorems.Rigidity.IdealTarget

/-!
# Coarse estimates and the large-error regime of Magic Square rigidity

The rigidity theorem `thm:ms-rigidity` asserts a bound at the scale
`C * (sqrt ε + sqrt δ)` with a universal constant `C`.  Once `sqrt ε + sqrt δ`
exceeds one, that scale exceeds `C`, and the assertion is carried by the trivial
estimates available for *any* witness: two unit vectors are at distance at most
two, the state-dependent distance between two contractions on a unit vector is
at most two, and a two-outcome family therefore has squared distance at most
eight.

This file collects those estimates together with the elementary isometry used to
build a witness for an arbitrary strategy: the embedding of a local space as the
fiber of the extracted register over one fixed basis vector.  The estimates are
stated for the one-point distribution and the binary alphabet in which the
rigidity conclusions are phrased.

## References

blueprint `thm:ms-rigidity`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`.
The distance conventions are blueprint
`def:povm-distance`, paper `06_nonlocal_games_and_mipstar.tex:258-285`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

/-! ## The fiber embedding of a local space in an extracted register -/

/-- Formalization-only linear embedding of a local space as the fiber of a
register over one fixed basis vector.  It is the coarse counterpart of the
swap isometries of `Rigidity/Swap.lean`, used to exhibit a witness of
`thm:ms-rigidity` for an arbitrary strategy in the regime where the asserted
bound is vacuous. -/
def registerFiberEmbeddingMap (κ ι : Type) [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι] (k : κ) :
    EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ (κ × ι) where
  toFun x := (EuclideanSpace.equiv (κ × ι) ℂ).symm
    (fun p => if p.1 = k then x p.2 else 0)
  map_add' x y := by
    ext p
    by_cases h : p.1 = k <;> simp [h]
  map_smul' c x := by
    ext p
    by_cases h : p.1 = k <;> simp [h]

/-- Formalization-only isometric embedding of a local space as the fiber of a
register over one fixed basis vector. -/
noncomputable def registerFiberEmbedding (κ ι : Type) [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι] (k : κ) :
    EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ (κ × ι) :=
  LinearMap.isometryOfInner (registerFiberEmbeddingMap κ ι k) <| by
    intro x y
    simp [PiLp.inner_apply, Fintype.sum_prod_type, registerFiberEmbeddingMap]

/-- The coordinates of the fiber embedding. -/
@[simp]
theorem registerFiberEmbedding_apply {κ ι : Type} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι] (k : κ) (x : EuclideanSpace ℂ ι) (p : κ × ι) :
    registerFiberEmbedding κ ι k x p = if p.1 = k then x p.2 else 0 := rfl

/-! ## Coarse contraction estimates -/

end

end MIPStarRE.QPBT.MagicSquareRigidity
