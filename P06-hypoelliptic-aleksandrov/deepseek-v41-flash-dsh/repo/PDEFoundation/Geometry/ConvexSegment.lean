module

public import PDEFoundation.Geometry.ConvexDomain

/-!
# Segment geometry in convex domains

This file provides the affine parametrization of a segment and the elementary
lemmas needed to keep that segment inside a convex domain. It contains no
Sobolev or Poincaré theory.

## Main definitions

- `PDE.segmentBlend`: the point with parameter `t` on the segment from `y` to `x`.

## Main results

- `PDE.segmentBlend_mem`: a segment between two points of a convex set stays in the set.
- `PDE.segmentBlend_mapsTo`: the corresponding `Set.MapsTo` statement.
- `PDE.ray_mem_of_endpoint_mem_of_isOpenBoundedConvexDomain`: a shorter point on a
  nonnegative ray remains in the domain when the endpoint does.
-/

@[expose] public section

namespace PDE

/-- The point on the segment from `y` to `x` with parameter `t`. -/
noncomputable def segmentBlend {d : ℕ} (x : Vec d) (t : ℝ) (y : Vec d) : Vec d :=
  AffineMap.lineMap y x t

@[simp]
theorem segmentBlend_eq_lineMap {d : ℕ} (x y : Vec d) (t : ℝ) :
    segmentBlend x t y = AffineMap.lineMap y x t :=
  rfl

@[simp]
theorem segmentBlend_zero {d : ℕ} (x y : Vec d) :
    segmentBlend x 0 y = y := by
  simp [segmentBlend]

@[simp]
theorem segmentBlend_one {d : ℕ} (x y : Vec d) :
    segmentBlend x 1 y = x := by
  simp [segmentBlend]

@[simp]
theorem segmentBlend_self {d : ℕ} (x : Vec d) (t : ℝ) :
    segmentBlend x t x = x := by
  simp [segmentBlend]
section
variable {d : ℕ} (x y : Vec d) (t : ℝ)

/-- The segment parametrization in basepoint-plus-displacement form. -/
theorem segmentBlend_eq_add_smul_sub  :
    segmentBlend x t y = y + t • (x - y) := by
  simpa [segmentBlend, add_comm] using
    (AffineMap.lineMap_apply_module' y x t)

/-- The segment parametrization as an affine combination of its endpoints. -/
theorem segmentBlend_eq_smul_add  :
    segmentBlend x t y = (1 - t) • y + t • x := by
  simpa [segmentBlend] using
    (AffineMap.lineMap_apply_module y x t)

theorem segmentBlend_sub_right  :
    segmentBlend x t y - y = t • (x - y) := by
  ext i
  simp [segmentBlend, AffineMap.lineMap_apply_module']

theorem norm_segmentBlend_sub_right  :
    ‖segmentBlend x t y - y‖ = |t| * ‖x - y‖ := by
  rw [segmentBlend_sub_right, norm_smul, Real.norm_eq_abs]
end

/-- A segment between two points of a convex set remains in the set. -/
theorem segmentBlend_mem {d : ℕ} {U : Set (Vec d)} (hU : Convex ℝ U)
    {x y : Vec d} (hx : x ∈ U) (hy : y ∈ U) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    segmentBlend x t y ∈ U := by
  simpa [segmentBlend] using hU.lineMap_mem hy hx ⟨ht0, ht1⟩

theorem segmentBlend_mem_of_isOpenBoundedConvexDomain {d : ℕ}
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {x y : Vec d} (hx : x ∈ U) (hy : y ∈ U) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    segmentBlend x t y ∈ U :=
  segmentBlend_mem hU.convex hx hy ht0 ht1

end PDE
