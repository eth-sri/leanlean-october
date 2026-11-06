module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionDensitySumPartition

/-! # Finiteness of the source starting-mass q-power sum -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory
open scoped ENNReal

variable (nu : Measure Point) (c : Clock)

/-- The starting-cell masses sum to the total starting mass. -/
theorem enlargedStartCell_mass_sum  (s x : ℝ)
    (hnu : ∀ᵐ e ∂nu, s ≤ e.time) :
    (∑' a : ℕ × ℤ, nu (enlargedStartCell c s x a.1 a.2)) = nu univ := by
  have h := congrArg (fun m : Measure Point => m univ)
    (enlargedStartCell_measure_sum nu c s x hnu)
  simp_all

/-- A finite starting measure has a finite q-power sum, bounded by its total mass to q. -/
theorem enlargedStartCell_power_sum_le  (s x q : ℝ)
    (hq : 1 ≤ q) (hnu : ∀ᵐ e ∂nu, s ≤ e.time) :
    (∑' a : ℕ × ℤ, nu (enlargedStartCell c s x a.1 a.2) ^ q) ≤ (nu univ) ^ q := by
  calc
    _ ≤ ∑' a : ℕ × ℤ, (nu univ) ^ (q - 1) *
        nu _ := by
      apply ENNReal.tsum_le_tsum
      intro a
      rw [← position_rpow_sub_one_mul _ q hq]
      exact mul_le_mul_left (ENNReal.rpow_le_rpow (measure_mono (subset_univ _))
        (sub_nonneg.mpr hq)) _
    _ = (nu univ) ^ (q - 1) * nu univ := by
      rw [ENNReal.tsum_mul_left, enlargedStartCell_mass_sum nu c s x hnu]
    _ = _ := position_rpow_sub_one_mul _ q hq

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
