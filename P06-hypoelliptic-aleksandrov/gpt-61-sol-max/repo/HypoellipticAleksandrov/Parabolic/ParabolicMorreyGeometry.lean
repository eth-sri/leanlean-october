module

public import HypoellipticAleksandrov.Parabolic.HarnackGeometry
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Parabolic coordinate geometry for Morrey regularity

This module introduces the time--velocity parabolic coordinate distance used
by the Morrey layer.  It deliberately retains the inherited topology and
metric structure on `TimeVelocity`; the distance is a quantitative tool, not
a new metric-space instance.
-/

@[expose] public section

open Filter Set

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

/-- The coordinate parabolic distance: square-root time separation and native
velocity-norm separation. -/
def parabolicCoordinateDist {d : Nat}
    (z w : TimeVelocity d) : Real :=
  max (Real.sqrt |z.1 - w.1|) ‖z.2 - w.2‖

variable {d : Nat}





/-- The parabolic coordinate distance is nonnegative. -/
theorem parabolicCoordinateDist_nonneg  (z w : TimeVelocity d) :
    0 ≤ parabolicCoordinateDist z w := by
  simp_all [parabolicCoordinateDist]

/-- The parabolic coordinate distance from a point to itself vanishes. -/
@[simp] theorem parabolicCoordinateDist_self  (z : TimeVelocity d) :
    parabolicCoordinateDist z z = 0 := by
  simp [parabolicCoordinateDist]

/-- The parabolic coordinate distance separates points. -/
@[simp] theorem parabolicCoordinateDist_eq_zero_iff
    (z w : TimeVelocity d) : parabolicCoordinateDist z w = 0 ↔ z = w := by
  let sharedTerm_a8adde94bd := ((Real.sqrt |z.1 - w.1|))
  constructor
  · intro h
    change max sharedTerm_a8adde94bd ‖z.2 - w.2‖ = 0 at h
    have htimeRoot : sharedTerm_a8adde94bd = 0 := by
      apply le_antisymm
      · simpa only [h] using le_max_left sharedTerm_a8adde94bd ‖z.2 - w.2‖
      · exact Real.sqrt_nonneg _
    have htimeAbs  :=
      (Real.sqrt_eq_zero (abs_nonneg _)).mp htimeRoot
    have htime  := sub_eq_zero.mp (abs_eq_zero.mp htimeAbs)
    have hvelocityNorm : ‖z.2 - w.2‖ = 0 := by
      apply le_antisymm
      · simp_all
      · exact norm_nonneg _
    have hvelocity  := sub_eq_zero.mp (norm_eq_zero.mp hvelocityNorm)
    exact Prod.ext htime hvelocity
  · rintro rfl
    exact parabolicCoordinateDist_self z







/-- Parabolic affine maps scale the coordinate distance by the absolute radius. -/
theorem parabolicCoordinateDist_parabolicAffine  (t0 : Real) (v0 : PDE.Vec d)
    (r : Real) (z w : TimeVelocity d) :
    parabolicCoordinateDist (parabolicAffine t0 v0 r z) (parabolicAffine t0 v0 r w) =
      |r| * parabolicCoordinateDist z w := by
  let sharedTerm_b2c72803bb := (t0 + r ^ 2 * z.1 - (t0 + r ^ 2 * w.1))
  let sharedTerm_77086a01a1 := ((v0 + r • z.2) - (v0 + r • w.2))
  have htime :
      Real.sqrt |(parabolicAffine t0 v0 r z).1 - (parabolicAffine t0 v0 r w).1| =
        |r| * Real.sqrt |z.1 - w.1| := by
    change Real.sqrt |sharedTerm_b2c72803bb| = _
    rw [show sharedTerm_b2c72803bb = r ^ 2 * (z.1 - w.1) by ring,
      abs_mul, abs_pow]
    calc
      Real.sqrt (|r| ^ 2 * |z.1 - w.1|) =
          Real.sqrt (|r| ^ 2) * Real.sqrt |z.1 - w.1| := by
        rw [Real.sqrt_mul (sq_nonneg |r|)]
      _ = |r| * Real.sqrt |z.1 - w.1| := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (abs_nonneg _)]
  have hvelocity :
      ‖(parabolicAffine t0 v0 r z).2 - (parabolicAffine t0 v0 r w).2‖ =
        |r| * ‖z.2 - w.2‖ := by
    change ‖sharedTerm_77086a01a1‖ = |r| * ‖z.2 - w.2‖
    rw [show sharedTerm_77086a01a1 = r • (z.2 - w.2) by module,
      norm_smul, Real.norm_eq_abs]
  unfold parabolicCoordinateDist
  rw [htime, hvelocity, ← mul_max_of_nonneg _ _ (abs_nonneg r)]



end

end HypoellipticAleksandrov.Parabolic
