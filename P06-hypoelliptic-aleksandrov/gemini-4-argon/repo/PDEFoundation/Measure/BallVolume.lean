module

public import PDEFoundation.Geometry.EuclideanBall
public import PDEFoundation.Measure.AffineVolume
public import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.Convex.Basic
import Mathlib.Basic.Real.Pointwise
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import PDEFoundation.Ambient.EuclideanNorm
import PDEFoundation.Geometry.Affine

/-!
# Volume of explicit round balls

Positivity, finiteness, and exact affine scaling for the native round-ball
geometry.
-/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped Pointwise

theorem volume_euclideanBall_ne_top {d }
    (x : Vec d) {R } (hR : 0 ≤ R) :
    volume (euclideanBall x R) ≠ ⊤ := by
  refine ne_top_of_le_ne_top
    ((isCompact_euclideanClosedBall x hR).measure_ne_top
      (μ := volume)) ?_
  exact measure_mono
    (euclideanBall_subset_euclideanClosedBall x R)

theorem volume_euclideanBall_pos {d }
    (x : Vec d) {R } (hR : 0 < R) :
    0 < volume (euclideanBall x R) :=
  (isOpen_euclideanBall x R).measure_pos volume
    (euclideanBall_nonempty x hR)

theorem volume_euclideanBall_toReal_pos {d }
    (x : Vec d) {R } (hR : 0 < R) :
    0 < (volume (euclideanBall x R)).toReal := by
  exact ENNReal.toReal_pos
    (volume_euclideanBall_pos x hR).ne'
    (volume_euclideanBall_ne_top x hR.le)

theorem volume_euclideanBall_eq_unit_mul_of_pos {d }
    (x : Vec d) {R } (hR : 0 < R) :
    volume (euclideanBall x R) =
      ENNReal.ofReal (R ^ d) *
        volume (euclideanBall (0 : Vec d) 1) := by
  have _h_xinl_0 : euclideanBall x R =
      translateSet x (R • euclideanBall (0 : Vec d) 1) := by
    ext z
    rw [mem_translateSet_iff_sub_mem]
    constructor
    · intro hz
      refine Set.mem_smul_set.2 ⟨R⁻¹ • (z - x), ?_, ?_⟩
      · have hpoint :
            R • (R⁻¹ • (z - x)) + x ∈
              euclideanBall x R := by
          have hpointEq :
              R • (R⁻¹ • (z - x)) + x = z := by
            ext i
            simp [hR.ne', sub_eq_add_neg]
          simpa [hpointEq] using hz
        exact
          (affine_mem_euclideanBall_iff_of_pos
            x (R⁻¹ • (z - x)) hR).1 hpoint
      · ext i
        simp [hR.ne']
    · intro hz
      rcases Set.mem_smul_set.1 hz with ⟨y, hy, hyEq⟩
      have hpoint :=
        (affine_mem_euclideanBall_iff_of_pos x y hR).2 hy
      have hpointEq : R • y + x = z := by
        ext i
        simp [hyEq, sub_eq_add_neg, add_assoc]
      simpa [hpointEq] using hpoint
  rw [_h_xinl_0,
    volume_translateSet_eq,
    volume_smul_set_of_nonneg hR.le]

end PDE
