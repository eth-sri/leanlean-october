/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Weighted.RadialKernel
public import BergmanWeakType.Weighted.PolarPotential
public import BergmanWeakType.Weighted.AngularMean

/-! # The circular normalizer as a polar kernel potential -/

@[expose] public section

noncomputable section

open MeasureTheory Real

namespace BergmanWeakType.Weighted

def boundaryPoint (t : ℝ) : ClosedDisk := ⟨circleMap 0 1 t, by simp⟩

abbrev boundarySource : PolarSource := angleMeasure.map boundaryPoint

theorem boundary_integral (α : ℝ) (z : ℂ) :
    ∫ w, ‖weightedKernel α z w.val‖ ∂boundarySource = normalizer α ‖z‖ := by
  change (∫ w : ClosedDisk, _ ∂angleMeasure.map boundaryPoint) = _
  rw [integral_map (by unfold boundaryPoint; fun_prop)]
  · simp only [boundaryPoint]; rw [integral_angle (fun w ↦ ‖weightedKernel α z w‖), circleAverage_weightedKernel_norm, one_mul]
  · apply Measurable.aestronglyMeasurable; measurability

theorem polarIntegral_boundary_eq_normalizer (α r θ : ℝ) :
    (boundarySource.field (-(α+2)/2)).val .v r θ = normalizer α r := by
  simp only [Field.val,Field.eval,PolarSource.field,PolarSource.avg,column_val,boundary_integral]; simp [radialMoment]

theorem ae_boundary_norm : ∀ᵐ w ∂boundarySource, ‖w.val‖ = 1 := by
  rw [ae_map_iff (by unfold boundaryPoint; fun_prop) (by measurability)]
  simp [boundaryPoint]

abbrev solution (α : ℝ) := (boundarySource.field (-(α+2)/2)).ray

@[simp] theorem solution_val (α r : ℝ) : (solution α).v r = normalizer α r := by
  simp only [Field.ray,angularMean,polarIntegral_boundary_eq_normalizer,integral_const,probReal_univ,one_smul]

theorem solution_eq (α : ℝ) {r : ℝ} (hr : r ∈ unitInterval) : (solution α).err (α+2) r = 0 := by
  rw [Field.ray_err _ _ hr]; apply integral_eq_zero_of_ae; exact .of_forall fun t ↦ boundarySource.error_boundary _ (inner_sq hr) hr.1.ne' t ae_boundary_norm

end BergmanWeakType.Weighted

namespace BergmanWeakType
open Weighted Set

/-- Comparison of the radial solution with the constant function. -/
theorem normalizer_mono (α : ℝ) : MonotoneOn (normalizer α) radii := by
  let B : Ray := ⟨1,0,0,continuousOn_const,continuousOn_const,fun _ _ ↦ ⟨hasDerivAt_const ..,hasDerivAt_const ..⟩⟩
  have H := (solution α).compare B (α+2) (α+2) 0 (-1) (by ring) (by ring) (by aesop) ?sub
  case sub =>
    intro r hr; rw [solution_eq α hr]; simp [B,Ray.err,rhs];
    have := normalizer_nonneg α r; have := sub_pos.mpr (inner_sq hr); positivity
  intro r hr R hR hle; simpa [B,driftWeight] using H hr hR hle

theorem normalizer_pos (α : ℝ) {r : ℝ} (hr : r ∈ radii) : 0 < normalizer α r :=
  lt_of_lt_of_le (by simp) (normalizer_mono α (by simp) hr hr.1)

private theorem solution_pos (α : ℝ) (r : ℝ) (hr : r ∈ radii) : 0 < (solution α).v r := by
  simpa using normalizer_pos α hr

theorem Weighted.Field.mean_comparison (F : Field) (α : ℝ) (L : ∀ r ∈ unitInterval, ∀ t, (F.eval r t).error (α+2) r ≤ 0) :
    AntitoneOn (fun r ↦ angularMean (F.val .v) r / normalizer α r) radii := by
  have H := F.ray.compare (solution α) (α+2) (α+2) 0 1 (by ring) (by ring) (solution_pos α) ?sub
  case sub =>
    intro r hr; rw [solution_eq α hr, F.ray_err _ hr]; simpa using
      mul_nonpos_of_nonneg_of_nonpos (solution_pos α r (Ioo_subset_Ico_self hr)).le (integral_nonpos (L r hr))
  change AntitoneOn (fun r ↦ F.ray.v r / normalizer α r) radii
  simpa [driftWeight] using H

/-- With complementary parameters both errors vanish: the normalized ratio
is simultaneously increasing and decreasing, hence equal to its value at zero. -/
theorem radial_transform (α : ℝ) {r : ℝ} (hr : r ∈ radii) :
    driftWeight (α+1) r * normalizer α r = normalizer (-α-2) r := by
  have H (s : ℝ) := (solution α).compare (solution (-α-2)) (α+2) (-α-2+2) (α+1) s (by ring) (by ring)
    (solution_pos _) (fun x hx ↦ by rw [solution_eq _ hx, solution_eq _ hx]; simp) (by simp) hr hr.1
  have h (s : ℝ) : s * driftWeight (α+1) r * normalizer α r ≤ s * normalizer (-α-2) r := by
    simpa [driftWeight, div_le_iff₀ (normalizer_pos (-α-2) hr)] using H s
  exact le_antisymm (by simpa using h 1) (by simpa using h (-1))

end BergmanWeakType
