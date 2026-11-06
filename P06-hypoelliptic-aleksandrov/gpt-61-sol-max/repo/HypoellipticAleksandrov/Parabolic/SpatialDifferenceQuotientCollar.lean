module

public import HypoellipticAleksandrov.Parabolic.SpatialDifferenceQuotient
public import Mathlib.Topology.MetricSpace.Thickening
import Aesop



/-!
# Compact-open collars for spatial shifts

This module gives the native product-metric collar required to keep compact
time--velocity supports inside an open set under small coordinate shifts.
-/

 public section

namespace HypoellipticAleksandrov.Parabolic



variable {d : ℕ}

/-- A coordinate spatial shift has native product-metric distance `|h|`. -/
theorem dist_spatialShift
     (k : Fin d) (h : ℝ) (z : TimeVelocity d) :
    dist (spatialShift k h z) z = |h| := by
  rcases z with ⟨t, y⟩
  rw [spatialShift_apply, dist_prod_same_left, dist_eq_norm]
  calc
    ‖y + h • PDE.basisVec k - y‖ = ‖h • PDE.basisVec k‖ := by
      rw [add_sub_cancel_left]
    _ = ‖h‖ * ‖PDE.basisVec k‖ := norm_smul _ _
    _ = |h| := by simp [PDE.basisVec, Pi.norm_single]

/-- A compact subset of an open time--velocity set has a positive native
collar stable under every coordinate shift of at most the collar radius. -/
theorem IsCompact.exists_spatialShift_cthickening_collar
     {K U : HypoellipticAleksandrov.Parabolic.Region d}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ K ⊆ U ∧
      ∀ (k : Fin d) (h : ℝ), |h| ≤ δ →
        Set.MapsTo (spatialShift k h) K U := by
  obtain ⟨δ, hδpos, hδ⟩ := hK.exists_cthickening_subset_open hU hKU
  refine ⟨δ, hδpos, hδ, ?_⟩
  intro k h hh z hz
  apply hδ
  exact Metric.mem_cthickening_of_dist_le (spatialShift k h z) z δ K hz
    (by simpa only [dist_spatialShift] using hh)

/-- A forward translate is supported in `U` when the corresponding backward
shift maps its original support carrier into `U`. -/
theorem tsupport_spatialTranslate_subset_of_mapsTo_spatialShift_neg
     {α : Type*} [Zero α] {K U : HypoellipticAleksandrov.Parabolic.Region d}
    (k : Fin d) (h : ℝ) (f : TimeVelocity d → α)
    (hfK : tsupport f ⊆ K)
    (hshift : Set.MapsTo (spatialShift k (-h)) K U) :
    tsupport (spatialTranslate k h f) ⊆ U := by
  intro z hz
  rw [tsupport_spatialTranslate] at hz
  change spatialShift k h z ∈ tsupport f at hz
  have hback  :=
    hshift (hfK hz)
  aesop

end HypoellipticAleksandrov.Parabolic
