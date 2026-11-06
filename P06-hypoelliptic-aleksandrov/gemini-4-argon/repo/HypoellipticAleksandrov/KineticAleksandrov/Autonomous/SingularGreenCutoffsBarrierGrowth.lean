module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsBarrierCutoff

/-! # Quantitative sublinear barrier growth on a kinetic cutoff rectangle -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous

/- The homogeneous position power on a cutoff rectangle is at most twice the radius. -/
theorem barrier_rectangle_position_power {alpha R x : ℝ} (ha : 0 ≤ alpha)
    (ha1 : alpha ≤ 1) (hR : 1 ≤ R) (hx : |x| ≤ 2 * R ^ 3) :
    |x| ^ (alpha / 3) ≤ 2 * R := by
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hbase : 1 ≤ 2 * R := by linarith only [hR]
  have hx3 : |x| ≤ (2 * R) ^ 3 := hx.trans (by nlinarith only [hR0, pow_nonneg hR0 3])
  have he : ((2 * R) ^ (3 : ℕ)) ^ (alpha / 3) = (2 * R) ^ alpha := by
    rw [← Real.rpow_natCast_mul (by positivity : 0 ≤ 2 * R)]
    congr 1
    ring
  exact ((Real.rpow_le_rpow (abs_nonneg x) hx3 (by linarith)).trans_eq he).trans
    (Real.rpow_le_self_of_one_le hbase ha1)

/- The velocity power on a cutoff rectangle is at most twice the radius. -/
theorem barrier_rectangle_velocity_power {alpha R v : ℝ} (ha : 0 ≤ alpha)
    (ha1 : alpha ≤ 1) (hR : 1 ≤ R) (hv : |v| ≤ 2 * R) :
    |v| ^ alpha ≤ 2 * R := by
  exact (Real.rpow_le_rpow (abs_nonneg v) hv ha).trans
    (Real.rpow_le_self_of_one_le (by linarith only [hR]) ha1)

/- A coordinate modulus gives a linear majorant on the kinetic rectangle.
The barrier degree is sublinear, so this bound is sufficient for errors of order R⁻¹. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
