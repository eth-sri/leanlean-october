module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.TruncationGeometry
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic.Linarith

/-!
# Open and bounded geometry of the actual straightened ellipsoid

These facts allow the scalar finite-cylinder maximum principle to be applied directly
on the truncations used by the truncated problems, without a full-domain solution premise.
-/

 public section



namespace HypoellipticAleksandrov.KineticAleksandrov

open Set


variable (n : ℕ) {r R : ℝ} (hr : 0 < r) (hR : 0 < R)

include hr hR
/-- The actual straightened ellipsoid is open. -/
theorem isOpen_straightenedEllipsoid  :
    IsOpen (openEllipsoid (straightenedEllipsoidMatrix n r R)) := by

  rw [(Set.ext fun x => (straightenedEllipsoid_characterization n r R hr hR).2 x)]
  exact isOpen_lt
    (((PDE.continuous_vecNormSq.comp (contDiff_spatialY (m := 0)).continuous).div_const _).add
      ((PDE.continuous_vecNormSq.comp (contDiff_spatialZ (m := 0)).continuous).div_const _))
    continuous_const

/-- The actual straightened ellipsoid is bounded in the inherited topology; its geometric
characterization still uses the Euclidean block norms. -/
theorem isBounded_straightenedEllipsoid  :
    Bornology.IsBounded (openEllipsoid (straightenedEllipsoidMatrix n r R)) := by
  let sharedTerm_ccd8173b47 := ((Metric.closedBall (0 : PDE.Vec n) r ×ˢ Metric.closedBall (0 : PDE.Vec n) R))
  let H := terminalCoordinateHomeomorph (0 : PDE.Vec n)
  have hc : IsCompact (H ⁻¹'
      sharedTerm_ccd8173b47) :=
    H.isCompact_preimage.mpr ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  refine hc.isBounded.subset ?_
  intro x hx
  have hsum := (straightenedEllipsoid_characterization n r R hr hR).2 x |>.mp hx


  have hball {s : ℝ} (hs : 0 < s) (y : PDE.Vec n) (hy : PDE.vecNormSq y < s ^ 2) :
      y ∈ Metric.closedBall (0 : PDE.Vec n) s := by
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hs.le]
    intro i
    rw [Real.norm_eq_abs]
    exact abs_le_of_sq_le_sq ((PDE.sq_apply_le_vecNormSq y i).trans hy.le) hs.le
  change (0 + spatialY x, spatialZ x) ∈
    sharedTerm_ccd8173b47
  simp only [zero_add, mem_prod]
  exact ⟨hball hr _ (show _ by
      have := div_nonneg (PDE.vecNormSq_nonneg (spatialZ x)) (sq_nonneg R)
      exact (div_lt_one (sq_pos_of_pos hr)).mp (by linarith)), hball hR _ (show _ by
      have := div_nonneg (PDE.vecNormSq_nonneg (spatialY x)) (sq_nonneg r)
      exact (div_lt_one (sq_pos_of_pos hR)).mp (by linarith))⟩

end HypoellipticAleksandrov.KineticAleksandrov
