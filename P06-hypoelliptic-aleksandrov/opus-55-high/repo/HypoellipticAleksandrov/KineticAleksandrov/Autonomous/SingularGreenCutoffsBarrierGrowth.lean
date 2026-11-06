module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.SingularGreenCutoffsBarrierCutoff

/-! # Quantitative sublinear barrier growth on a kinetic cutoff rectangle -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous

/-- The homogeneous position power on a cutoff rectangle is at most twice the radius. -/
theorem barrier_rectangle_position_power {alpha R x : ℝ} (ha : 0 ≤ alpha)
    (ha1 : alpha ≤ 1) (hR : 1 ≤ R) (hx : |x| ≤ 2 * R ^ 3) :
    |x| ^ (alpha / 3) ≤ 2 * R := by
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hbase : 1 ≤ 2 * R := by linarith
  have hx3 : |x| ≤ (2 * R) ^ 3 := hx.trans (by grind)
  have he : ((2 * R) ^ (3)) ^ (alpha / 3) = (2 * R) ^ alpha := by
    rw [← Real.rpow_natCast_mul (by positivity)]
    ring
  exact ((Real.rpow_le_rpow (abs_nonneg x) hx3 (by linarith)).trans_eq he).trans
    (Real.rpow_le_self_of_one_le hbase ha1)

/-- The velocity power on a cutoff rectangle is at most twice the radius. -/
theorem barrier_rectangle_velocity_power {alpha R v : ℝ} (ha : 0 ≤ alpha)
    (ha1 : alpha ≤ 1) (hR : 1 ≤ R) (hv : |v| ≤ 2 * R) :
    |v| ^ alpha ≤ 2 * R := (Real.rpow_le_rpow (abs_nonneg v) hv ha).trans
    (Real.rpow_le_self_of_one_le (by linarith) ha1)

/-- A coordinate modulus gives a linear majorant on the kinetic rectangle.
The barrier degree is sublinear, so this bound is sufficient for errors of order R⁻¹. -/
theorem barrier_rectangle_growth (f : (ℝ × ℝ) → ℝ) (alpha D : ℝ)
    (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1) (hD : 0 ≤ D)
    (hm : ∀ z w : ℝ × ℝ, |f z - f w| ≤
      D * (|z.1 - w.1| ^ (alpha / 3) + |z.2 - w.2| ^ alpha))
    (Y R : ℝ) (hR : 1 ≤ R) (z : ℝ × ℝ)
    (hx : |z.1 - Y| ≤ 2 * R ^ 3) (hv : |z.2| ≤ 2 * R) :
    |f z| ≤ (|f (Y, 0)| + 4 * D) * R := by
  have hh := hm z (Y, 0)
  simp only [sub_zero] at hh
  have hpx := barrier_rectangle_position_power ha ha1 hR hx
  have hpv := barrier_rectangle_velocity_power ha ha1 hR hv
  have hbound : |f z - f _| ≤ D * (4 * R) :=
    hh.trans (mul_le_mul_of_nonneg_left (by linarith) hD)
  have hcenter : |f (Y, 0)| ≤ |f (Y, 0)| * R := by
    simpa using mul_le_mul_of_nonneg_left hR (abs_nonneg _)
  grind

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
