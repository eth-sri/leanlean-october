/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.FiniteGridTransferBounded
public import DOZZ.Hypergeom.ODE.LocalTransfer

/-! A grid of local Picard transfers is homotopy invariant when each cell lies near its lower-left
vertex and the two vertical boundary paths are constant. -/

@[expose] public section

namespace DOZZ.Proofs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem localPicard_homotopy_grid_endpoint_eq
    N r M (hr : 0 < r) (hM : 0 ≤ M)
    (H : ℂ → E →L[ℂ] E) (node : ℕ → ℕ → ℂ)
    (data : ∀ i ≤ N, ∀ j ≤ N, LocalHolomorphicODEData r M H (node i j))
    (hcell : ∀ i < N, ∀ j < N,
      dist (node (i + 1) j) (node i j) < r / 4 ∧
      dist (node i (j + 1)) (node i j) < r / 4 ∧
      dist (node (i + 1) (j + 1)) (node i j) < r / 4)
    (hleft : ∀ j ≤ N, node 0 j = node 0 0)
    (hright : ∀ j ≤ N, node N j = node N 0)
    (y : E) :
    let right : ℕ → ℕ → E → E := fun i j v =>
      if hi : i < N then
        if hj : j ≤ N then
          localPicardTransfer r M H (data i (Nat.le_of_lt hi) j hj) v (node (i + 1) j)
        else v
      else v
    finiteGridHorizontal right 0 0 N y = finiteGridHorizontal right 0 N N y := by
  dsimp
  let right : ℕ → ℕ → E → E := fun i j v =>
    if hi : i < N then
      if hj : j ≤ N then
        localPicardTransfer r M H (data i (Nat.le_of_lt hi) j hj) v (node (i + 1) j)
      else v
    else v
  let up : ℕ → ℕ → E → E := fun i j v =>
    if hi : i ≤ N then
      if hj : j < N then
        localPicardTransfer r M H (data i hi j (Nat.le_of_lt hj)) v (node i (j + 1))
      else v
    else v
  have hsquare : ∀ i < N, ∀ j < N, ∀ v,
      up (i + 1) j (right i j v) = right i (j + 1) (up i j v) := by
    intro i hi j hj v
    have hiN := Nat.succ_le_iff.mpr hi
    have hjN := Nat.succ_le_iff.mpr hj
    simpa [right, up, hi, hiN, hj, hjN, Nat.le_of_lt hi, Nat.le_of_lt hj] using (localPicardTransfer_square_commutes r M hr hM H (data i (by omega) j (by omega)) (data (i + 1) hiN j (by omega)) (data i (by omega) (j + 1) hjN) (hcell i hi j hj).1 (hcell i hi j hj).2.1 (hcell i hi j hj).2.2 v)
  simpa [right] using (finiteGrid_boundary_transfer_eq_of_bounded_squares N right up hsquare (by intro j hj v; simp [up, hj, (hleft j (Nat.le_of_lt hj)), (hleft (j + 1) (by omega)), localPicardTransfer, holomorphicPicardSolution_apply_center]) (by intro j hj v; simp [up, hj, (hright j (by omega)), (hright (j + 1) (by omega)), localPicardTransfer, holomorphicPicardSolution_apply_center]) y)

end DOZZ.Proofs
