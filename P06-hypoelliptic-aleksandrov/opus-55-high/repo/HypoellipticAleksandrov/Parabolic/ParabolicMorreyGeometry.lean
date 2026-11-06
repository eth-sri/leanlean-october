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
noncomputable def parabolicCoordinateDist {d : Nat}
    (z w : TimeVelocity d) : Real :=
  max (Real.sqrt |z.1 - w.1|) ‖z.2 - w.2‖

/-- The open coordinate box of parabolic radius `r` about `z0`. -/
def parabolicCoordinateBox {d : Nat} (z0 : TimeVelocity d) (r : Real) :
    Set (TimeVelocity d) :=
  {z | parabolicCoordinateDist z z0 < r}

variable {d : Nat} (z w : TimeVelocity d)

/-- The parabolic coordinate distance is nonnegative. -/
theorem parabolicCoordinateDist_nonneg  :
    0 ≤ parabolicCoordinateDist z w := le_trans (Real.sqrt_nonneg _) (le_max_left _ _)

/-- The parabolic coordinate distance from a point to itself vanishes. -/
@[simp] theorem parabolicCoordinateDist_self  (z : TimeVelocity d) :
    parabolicCoordinateDist z z = 0 := by
  simp [parabolicCoordinateDist]

/-- The parabolic coordinate distance separates points. -/
@[simp] theorem parabolicCoordinateDist_eq_zero_iff  : parabolicCoordinateDist z w = 0 ↔ z = w := by
  constructor
  · intro h
    change max (Real.sqrt |z.1 - w.1|) ‖z.2 - w.2‖ = 0 at h
    have htimeRoot : Real.sqrt |z.1 - w.1| = 0 := by
      apply le_antisymm
      · grind
      positivity
    have htimeAbs : |z.1 - w.1| = 0 :=
      (Real.sqrt_eq_zero (abs_nonneg _)).mp htimeRoot
    have htime : z.1 = w.1 := sub_eq_zero.mp (abs_eq_zero.mp htimeAbs)
    have hvelocityNorm : ‖z.2 - w.2‖ = 0 := by
      simp_all
    have hvelocity : z.2 = w.2 := sub_eq_zero.mp (norm_eq_zero.mp hvelocityNorm)
    grind
  simp_all

/-- Membership in a parabolic coordinate box is its defining strict inequality. -/
@[simp] theorem mem_parabolicCoordinateBox_iff  {z z0 : TimeVelocity d} {r : Real} :
    z ∈ parabolicCoordinateBox z0 r ↔ parabolicCoordinateDist z z0 < r :=
  Iff.rfl

/-- Parabolic affine maps scale the coordinate distance by the absolute radius. -/
theorem parabolicCoordinateDist_parabolicAffine  (t0 : Real) (v0 : PDE.Vec d)
    (r : Real) (z w : TimeVelocity d) :
    parabolicCoordinateDist (parabolicAffine t0 v0 r z) (parabolicAffine t0 v0 r w) =
      |r| * parabolicCoordinateDist z w := by
  have htime :
      Real.sqrt |(parabolicAffine t0 v0 r z).1 - (parabolicAffine t0 v0 r w).1| =
        |r| * Real.sqrt |z.1 - w.1| := by
    change Real.sqrt |t0 + r ^ 2 * z.1 - (t0 + r ^ 2 * w.1)| = _
    rw [show t0 + r ^ 2 * z.1 - (t0 + r ^ 2 * w.1) = r ^ 2 * (z.1 - w.1) by ring,
      abs_mul, abs_pow]
    calc
      Real.sqrt _ =
          Real.sqrt (|r| ^ 2) * Real.sqrt |z.1 - w.1| := by
        simp
      _ = |r| * Real.sqrt _ := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (abs_nonneg _)]
  have hvelocity :
      ‖(parabolicAffine t0 v0 r z).2 - (parabolicAffine t0 v0 r w).2‖ =
        |r| * ‖z.2 - w.2‖ := by
    change ‖(v0 + r • z.2) - (v0 + r • w.2)‖ = |r| * ‖z.2 - w.2‖
    rw [show (v0 + r • z.2) - (v0 + r • w.2) = r • (z.2 - w.2) by module,
      norm_smul, Real.norm_eq_abs]
  unfold parabolicCoordinateDist
  rw [htime, hvelocity, ← mul_max_of_nonneg _ _ (abs_nonneg r)]

namespace ParabolicHolderSeminormLE

end ParabolicHolderSeminormLE

end

end HypoellipticAleksandrov.Parabolic
