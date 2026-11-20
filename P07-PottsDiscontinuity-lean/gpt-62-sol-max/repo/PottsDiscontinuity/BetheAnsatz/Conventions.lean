module

public import PottsDiscontinuity.BetheAnsatz.Defs
public import PottsDiscontinuity.SixVertex.TransferMatrix

/-!
# Coordinates, nonzero amplitudes, and the full-matrix/block bridge

The paper's positions `1,...,N` are our increasing `Fin N` positions plus one.
The resulting uniform phase is exactly `exp(i ∑j p_j)`, independently of the state.
The block-extension identity below is linear algebra for arbitrary vectors; it does not
assert the Bethe Ansatz for an unproved particle sector.
-/

@[expose] public section

open Finset Complex Matrix

namespace PottsDiscontinuity.BetheAnsatz

open SixVertex

/-- Evaluation of the full matrix on a zero-extended vector agrees with the block action. -/
theorem mulVec_extendByZero_apply {N n : ℕ} (c : ℝ) (v : State N n → ℂ)
    (x : State N n) :
    ((transferMatrix N c).map (algebraMap ℝ ℂ) *ᵥ extendByZero v) x.1 =
      ((transferBlock N c n).map (algebraMap ℝ ℂ) *ᵥ v) x := by
  classical
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr_set {y : Finset (Fin N) | y.card = n}
  · intro y hy
    change y.card = n at hy
    simp [transferBlock_apply, extendByZero, hy]
  · intro y hy
    simp_all

end PottsDiscontinuity.BetheAnsatz
