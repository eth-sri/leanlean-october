module

public import PottsDiscontinuity.BetheAnsatz.GapGeometric
public import PottsDiscontinuity.BetheAnsatz.GapInclusionExclusion

/-!
# Restricted cyclic gap sums

The constraints on a collision set separate coordinate by coordinate. Unlike the
printed `eq:ArbitrarySetCalc`, the formula below includes adjacent collisions:
the corresponding local factor is zero, since every gap has positive length.
-/

public section

open Finset Complex Classical

namespace PottsDiscontinuity.BetheAnsatz

section
variable {N n : ℕ}
/-- Collision constraints expressed at each individual coordinate. -/
theorem gapCollision_constraints_iff (x y : Fin (n + 1) → ℤ)
    (S : Finset (Fin (n + 1))) :
    (∀ k ∈ S, gapCollision N x y k) ↔
      ∀ k, (k ∈ S → y k = x k) ∧
        ((finRotate (n + 1)).symm k ∈ S → y k = cyclicPredecessorPositions N x k) := by
  grind [gapCollision]

/-- Product domain for a collision set, including the empty domain when constraints conflict. -/
theorem restricted_gapTuples_eq_pi (x : Fin (n + 1) → ℤ)
    (S : Finset (Fin (n + 1))) :
    (gapTuples N x).filter (fun y => ∀ k ∈ S, gapCollision N x y k) =
      Fintype.piFinset (fun k => (Icc (cyclicPredecessorPositions N x k) (x k)).filter
        (fun u => (k ∈ S → u = x k) ∧
          ((finRotate (n + 1)).symm k ∈ S → u = cyclicPredecessorPositions N x k))) := by
  ext y
  simp only [mem_filter, mem_gapTuples, gapCollision_constraints_iff,
    Fintype.mem_piFinset, mem_Icc]
  grind
end

/-- Evaluate one gap with either, both, or neither endpoint forced. -/
theorem sum_constrained_gap_geometric (c p : ℝ) {a b : ℤ} (hab : a < b)
    (hp : z p ≠ 1) (A B : Prop) :
    (∑ u ∈ (Icc a b).filter (fun u => (A → u = b) ∧ (B → u = a)),
      (if u = a ∨ u = b then (1 : ℂ) else (c : ℂ) ^ 2) * positionPhase p u) =
      if A then (if B then 0 else positionPhase p b)
      else (if B then positionPhase p a
        else L c (z p) * positionPhase p a + M c (z p) * positionPhase p b) := by
  by_cases hA : A <;> by_cases hB : B
  · have he : (Icc a b).filter (fun u => (A → u = b) ∧ (B → u = a)) = ∅ := by
      grind
    grind
  · have he : (Icc a b).filter (fun u => (A → u = b) ∧ (B → u = a)) = {b} := by
      grind
    simp_all
  · have he : (Icc a b).filter (fun u => (A → u = b) ∧ (B → u = a)) = {a} := by
      grind
    simp_all
  · simpa only [hA, hB, false_implies, and_self, filter_true, ↓reduceIte] using
      sum_gap_geometric c p hab hp

section
variable {N n : ℕ}
/-- Strictly positive lengths of the predecessor gaps. -/
theorem cyclicPredecessorPositions_lt {x : Fin (n + 1) → ℤ}
    (hx : StrictMono x) (hspan : x (Fin.last n) - x 0 < (N : ℤ)) (k : Fin (n + 1)) :
    cyclicPredecessorPositions N x k < x k := by
  induction k using Fin.cases with
  | zero => simp; omega
  | succ k =>
    aesop

/-- Equation `eq:ArbitrarySetCalc`, extended to every collision set by zero factors. -/
theorem restrictedGapSum_eq_product (c : ℝ) (x : Fin (n + 1) → ℤ)
    (p : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin (n + 1)))
    (S : Finset (Fin (n + 1))) (hx : StrictMono x)
    (hspan : x (Fin.last n) - x 0 < (N : ℤ)) (hp : ∀ j, z (p j) ≠ 1) :
    restrictedGapSum (N := N) c x p σ S =
      ∏ k, if k ∈ S then
        (if (finRotate (n + 1)).symm k ∈ S then 0 else positionPhase (p (σ k)) (x k))
      else (if (finRotate (n + 1)).symm k ∈ S then
        positionPhase (p (σ k)) (cyclicPredecessorPositions N x k)
      else L c (z (p (σ k))) * positionPhase (p (σ k)) (cyclicPredecessorPositions N x k) +
        M c (z (p (σ k))) * positionPhase (p (σ k)) (x k)) := by
  unfold restrictedGapSum
  rw [restricted_gapTuples_eq_pi]
  unfold gapWeight planeWave
  simp_rw [← Finset.prod_mul_distrib]
  change (∑ y ∈ Fintype.piFinset _, ∏ k,
    (if y k = cyclicPredecessorPositions N x k ∨ y k = x k then (1 : ℂ) else (c : ℂ) ^ 2) *
      positionPhase (p (σ k)) (y k)) = _
  rw [← Finset.prod_univ_sum
    (fun k => (Icc (cyclicPredecessorPositions N x k) (x k)).filter
      (fun u => (k ∈ S → u = x k) ∧
        ((finRotate (n + 1)).symm k ∈ S → u = cyclicPredecessorPositions N x k)))
    (fun k (u : ℤ) => (if u = cyclicPredecessorPositions N x k ∨ u = x k
      then (1 : ℂ) else (c : ℂ) ^ 2) * positionPhase (p (σ k)) u)]
  apply Finset.prod_congr rfl
  intro k _
  have hlocal := sum_constrained_gap_geometric c (p (σ k))
    (cyclicPredecessorPositions_lt hx hspan k) (hp (σ k))
    (k ∈ S) ((finRotate (n + 1)).symm k ∈ S)
  simp_all
end

end PottsDiscontinuity.BetheAnsatz
