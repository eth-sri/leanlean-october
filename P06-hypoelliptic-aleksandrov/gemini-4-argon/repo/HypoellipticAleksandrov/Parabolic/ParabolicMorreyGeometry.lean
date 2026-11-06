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

/- The coordinate parabolic distance: square-root time separation and native
velocity-norm separation. -/
noncomputable def parabolicCoordinateDist {d }
    (z w : TimeVelocity d) : Real :=
  max (Real.sqrt |z.1 - w.1|) ‖z.2 - w.2‖

/- The open coordinate box of parabolic radius `r` about `z0`. -/
def ParabolicHolderSeminormLE {d } (S : Set (TimeVelocity d))
    (u : TimeVelocity d -> Real) (alpha K : Real) : Prop :=
  ∀ z ∈ S, ∀ w ∈ S,
    |u z - u w| <= K * parabolicCoordinateDist z w ^ alpha

/- The parabolic coordinate distance is nonnegative. -/
theorem parabolicCoordinateDist_nonneg {d } (z w : TimeVelocity d) :
    0 ≤ parabolicCoordinateDist z w := by
  unfold parabolicCoordinateDist
  exact le_trans (Real.sqrt_nonneg _) (le_max_left _ _)

/- The parabolic coordinate distance from a point to itself vanishes. -/
@[simp] theorem parabolicCoordinateDist_self {d } (z : TimeVelocity d) :
    parabolicCoordinateDist z z = 0 := by
  simp [parabolicCoordinateDist]

/- The parabolic coordinate distance separates points. -/
@[simp] theorem parabolicCoordinateDist_eq_zero_iff {d }
    (z w : TimeVelocity d) : parabolicCoordinateDist z w = 0 ↔ z = w := by
  constructor
  · intro h
    change max (Real.sqrt |z.1 - w.1|) ‖z.2 - w.2‖ = 0 at h
    have htimeRoot : Real.sqrt |z.1 - w.1| = 0 := by
      apply le_antisymm
      · simpa only [h] using le_max_left (Real.sqrt |z.1 - w.1|) ‖z.2 - w.2‖
      · exact Real.sqrt_nonneg _
    have htimeAbs : |z.1 - w.1| = 0 :=
      (Real.sqrt_eq_zero (abs_nonneg _)).mp htimeRoot
    have htime : z.1 = w.1 := sub_eq_zero.mp (abs_eq_zero.mp htimeAbs)
    have hvelocityNorm : ‖z.2 - w.2‖ = 0 := by
      apply le_antisymm
      · simpa only [h] using le_max_right (Real.sqrt |z.1 - w.1|) ‖z.2 - w.2‖
      · exact norm_nonneg _
    have hvelocity : z.2 = w.2 := sub_eq_zero.mp (norm_eq_zero.mp hvelocityNorm)
    exact Prod.ext htime hvelocity
  · rintro rfl
    exact parabolicCoordinateDist_self z

/- The parabolic coordinate distance is continuous in the inherited product topology. -/
theorem parabolicCoordinateDist_parabolicAffine {d } (t0 : Real) (v0 : PDE.Vec d)
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
      Real.sqrt (|r| ^ 2 * |z.1 - w.1|) =
          Real.sqrt (|r| ^ 2) * Real.sqrt |z.1 - w.1| := by
        rw [Real.sqrt_mul (sq_nonneg |r|)]
      _ = |r| * Real.sqrt |z.1 - w.1| := by
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

/- A positive-exponent parabolic Hölder bound yields continuity on its set. -/
end ParabolicHolderSeminormLE

end

end HypoellipticAleksandrov.Parabolic
