module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionOverlapMixture
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionOverlapCells

/-! # Canonical decomposition into disjoint time-position starting cells -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory


variable (c : Clock) (s x : ℝ)

/-- The two-index source cells form a pairwise disjoint grid. -/
theorem enlargedStartCell_pairwiseDisjoint  :
    Pairwise (fun a b : ℕ × ℤ =>
      Disjoint (enlargedStartCell c s x a.1 a.2) (enlargedStartCell c s x b.1 b.2)) := (fun ⦃a b⦄ hab =>
  disjoint_left.mpr fun ⦃p⦄ ha hb =>
    if ht : a.1 = b.1 then
      disjoint_left.mp (enlargedPositionCell_disjoint c.r x c.positive fun hk => hab (Prod.ext ht hk)) ha.right hb.right
    else disjoint_left.mp (enlargedTimeBin_disjoint c.r s c.positive ht) ha.left hb.left)

/-- The time-position grid covers all starting points on and after its time origin. -/
theorem enlargedStartCell_iUnion  :
    (⋃ a : ℕ × ℤ, enlargedStartCell c s x a.1 a.2) = {p | s ≤ p.time} := by
  ext p
  constructor
  · intro hp
    obtain ⟨a, ha⟩ := mem_iUnion.mp hp

    have hj : 0 ≤ (a.1 : ℝ) := Nat.cast_nonneg _
    change s ≤ p.time
    exact (le_add_of_nonneg_right (mul_nonneg hj (sq_nonneg c.r))).trans ((enlargedTimeBin_bounds c.r s p.time a.1 ha.1).1)
  · intro hp
    obtain ⟨j, hj⟩ := enlargedTimeBin_covers c.r s p.time c.positive hp
    obtain ⟨k, hk⟩ := enlargedPositionCell_covers c.r x (p.position 0) c.positive
    exact mem_iUnion.mpr ⟨(j, k), hj, hk⟩

/-- A positive starting measure after the origin is the sum of its cell restrictions. -/
theorem enlargedStartCell_measure_sum (nu : Measure Point) (c : Clock) (s x : ℝ)
    (hnu : ∀ᵐ e ∂nu, s ≤ e.time) :
    nu = Measure.sum (fun a : ℕ × ℤ => nu.restrict (enlargedStartCell c s x a.1 a.2)) := (Eq.trans
  (Eq.symm
    (Eq.mpr (id (congrArg (fun _a => nu.restrict _a = nu) (enlargedStartCell_iUnion c s x)))
      (Measure.restrict_eq_self_of_ae_mem hnu)))
  (Measure.restrict_iUnion (enlargedStartCell_pairwiseDisjoint c s x) fun a =>
    measurableSet_enlargedStartCell c s x a.1 a.2))

/-- The actual positive mixture density decomposes into the same source-cell mixtures. -/
theorem positionMixtureDensity_sum_cells
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (nu : Measure Point) (s x : ℝ)
    (hnu : ∀ᵐ e ∂nu, s ≤ e.time) :
    positionMixtureDensity hH hLE hlam hLam A c nu =
      fun z => ∑' a : ℕ × ℤ, positionMixtureDensity hH hLE hlam hLam A c
        (nu.restrict (enlargedStartCell c s x a.1 a.2)) z := by
  calc
    _ = positionMixtureDensity hH hLE hlam hLam A c
        (Measure.sum (fun a : ℕ × ℤ => nu.restrict
          (enlargedStartCell c s x a.1 a.2))) :=
      congrArg _
        (enlargedStartCell_measure_sum nu c s x hnu)
    _ = _ := by
      funext z
      exact lintegral_sum_measure _ _

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
