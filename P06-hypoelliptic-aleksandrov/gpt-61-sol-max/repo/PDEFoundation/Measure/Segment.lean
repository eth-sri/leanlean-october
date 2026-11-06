module

public import PDEFoundation.Geometry.ConvexSegment
public import PDEFoundation.Measure.AffineVolume

/-!
# Integration along affine segment maps

Exact change of variables for the map sending `y` to the point with parameter
`t` on the segment from `y` to a fixed point `x`.  Convexity then controls the
image of the first half of every such segment.
-/

 public section

namespace PDE

open MeasureTheory
open scoped Pointwise

variable {d : ℕ}

private theorem segmentBlend_eq_smul_sub_add
    (x y : Vec d) (t : ℝ) :
    segmentBlend x t y = (1 - t) • (y - x) + x := by
  rw [segmentBlend_eq_smul_add]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- Exact change of variables under segment blending toward a fixed point.

For `t < 1`, the map `y ↦ segmentBlend x t y` has linear part
`(1 - t) • id`, image
`translateSet x ((1 - t) • translateSet (-x) U)`, and inverse-Jacobian factor
`((1 - t) ^ d)⁻¹`. -/
theorem setIntegral_comp_segmentBlend_of_lt_one
     {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (x : Vec d) {t : ℝ} (ht : t < 1) (U : Set (Vec d))
    (φ : Vec d → E) :
    ∫ y in U, φ (segmentBlend x t y) =
      ((1 - t) ^ d)⁻¹ •
        ∫ z in translateSet x
          ((1 - t) • translateSet (-x) U), φ z := by
  let sharedTerm_412c839b45 := (((1 - t) • translateSet (-x) U))

  have hIntegrand :
      (fun y  => φ (segmentBlend x t y)) =
        fun y => φ ((1 - t) • (y + -x) + x) := by
    funext y
    rw [segmentBlend_eq_smul_sub_add]
    rfl
  rw [hIntegrand]
  calc
    (∫ y in U, φ ((1 - t) • (y + -x) + x)) =
        ∫ z in translateSet (-x) U,
          φ ((1 - t) • z + x) :=
      setIntegral_comp_addRight_translateSet
        (-x) U (fun z => φ ((1 - t) • z + x))
    _ = ((1 - t) ^ d)⁻¹ •
        ∫ w in sharedTerm_412c839b45,
          φ (w + x) :=
      setIntegral_comp_smul_of_pos (sub_pos.mpr ht)
        _ (fun w => φ (w + x))
    _ = ((1 - t) ^ d)⁻¹ •
        ∫ z in translateSet x
          sharedTerm_412c839b45, φ z := by
      rw [setIntegral_comp_addRight_translateSet]

/-- On the first half of segments toward a point of a convex set, composition
costs at most the dimensionally sharp Jacobian factor `2 ^ d`.

The integrand is assumed nonnegative everywhere and integrable on `U`; no
diameter or boundedness hypothesis is involved. -/
theorem setIntegral_comp_segmentBlend_le_two_pow_mul
     {U : Set (Vec d)} {φ : Vec d → ℝ}
    {x : Vec d} {t : ℝ} (hU : Convex ℝ U) (hx : x ∈ U)
    (ht0 : 0 ≤ t) (htHalf : t ≤ (1 / 2 : ℝ))
    (hφ : IntegrableOn φ U ) (hφNonneg : ∀ y, 0 ≤ φ y) :
    ∫ y in U, φ (segmentBlend x t y) ≤
      (2 : ℝ) ^ d * ∫ y in U, φ y := by
  let sharedTerm_a5dcc000a0 := (((1 - t) ^ d)⁻¹)
  let sharedTerm_28720d1bb8 := (∫ y in U, φ y ∂volume)
  have htOne : t < 1 := by
    linarith

  have hscale  := sub_pos.mpr htOne
  let V  :=
    translateSet x ((1 - t) • translateSet (-x) U)

  have hIntegralMono  :=
    setIntegral_mono_set hφ
      (ae_restrict_of_ae (Filter.Eventually.of_forall hφNonneg))
      (show V ⊆ U by
          intro z hz
          rcases hz with ⟨w, hw, rfl⟩
          rcases Set.mem_smul_set.mp hw with ⟨v, hv, rfl⟩
          rcases hv with ⟨y, hy, rfl⟩
          have hsegment  :=
            segmentBlend_mem hU hx hy ht0 htOne.le
          have heq :
              (1 - t) • (y + -x) + x = segmentBlend x t y := by
            rw [segmentBlend_eq_smul_sub_add]
            rfl
          rw [heq]
          exact hsegment).eventuallyLE
  have hIntegralNonneg : 0 ≤ ∫ z in V, φ z :=
    setIntegral_nonneg_of_ae
      (Filter.Eventually.of_forall hφNonneg)


  rw [setIntegral_comp_segmentBlend_of_lt_one x htOne U φ]
  change
    sharedTerm_a5dcc000a0 * (∫ z in V, φ z) ≤
      (2 : ℝ) ^ d * sharedTerm_28720d1bb8
  calc
    sharedTerm_a5dcc000a0 * (∫ z in V, φ z) ≤
        (2 : ℝ) ^ d * (∫ z in V, φ z) :=
      mul_le_mul_of_nonneg_right (by
          calc
            sharedTerm_a5dcc000a0 = ((1 - t)⁻¹) ^ d :=
              (inv_pow (1 - t) d).symm
            _ ≤ (2 : ℝ) ^ d :=
              pow_le_pow_left₀ (inv_nonneg.mpr hscale.le) (by
                  rw [inv_le_iff_one_le_mul₀' hscale]
                  linarith) d) hIntegralNonneg
    _ ≤ (2 : ℝ) ^ d * sharedTerm_28720d1bb8 :=
      mul_le_mul_of_nonneg_left hIntegralMono (pow_nonneg (by norm_num) d)

end PDE
