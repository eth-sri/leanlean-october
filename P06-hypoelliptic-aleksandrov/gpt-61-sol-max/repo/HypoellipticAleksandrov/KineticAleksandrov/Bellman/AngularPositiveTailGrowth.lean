module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularPositiveTailDivergence
import Mathlib.Tactic

/-! # The angular tail rules out a positive linear growth limit -/

 public section

namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Filter
open scoped Topology

/-- Ellipticity and the finite tail exclude a positive limit of h(y)/y. -/
theorem bellmanAngularTail_no_positive_linear_limit (R β : ℝ) (hR : 1 ≤ R) (hβ : 3 ≤ β)
    (f h : ℝ → ℝ)
    (htail : IntegrableOn (fun y => f y * |y| ^ (β - 4)) {y : ℝ | 2 < |y|} volume)
    (hcomp : ∀ᵐ y, h y ≤ R * f y) (L : ℝ) (hL : 0 < L)
    (hlim : Tendsto (fun y => h y / y) atTop (𝓝 L)) : False := by


  obtain ⟨a, ha⟩ := eventually_atTop.mp (hlim.eventually (eventually_gt_nhds (by linarith : L / 2 < L)))



  apply bellmanAngularTail_not_power_lower_bound f β (max 2 a) (L / (2 * R)) (β - 3)
    htail (le_max_left _ _) (div_pos hL (by positivity)) (by linarith)
  filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae hcomp] with y hy hcy
  have hyp : 0 < y := by have := (le_max_left 2 a).trans hy.le; linarith

  have hly  := (lt_div_iff₀ hyp).mp (ha y ((le_max_right 2 a).trans hy.le))


  have hp : y * y ^ (β - 4) = y ^ (β - 3) := by
    calc
      y * y ^ (β - 4) = y ^ (1 : ℝ) * y ^ (β - 4) := by rw [Real.rpow_one]
      _ = y ^ (1 + (β - 4)) := (Real.rpow_add hyp _ _).symm
      _ = y ^ (β - 3) := by congr 1; ring
  calc
    (L / (2 * R)) * y ^ (β - 3) =
        ((L / (2 * R)) * y) * y ^ (β - 4) := by rw [mul_assoc, hp]
    _ ≤ _ := (mul_le_mul_of_nonneg_right (by
        have heq : R * ((L / (2 * R)) * y) = L / 2 * y := by field_simp
        rw [← heq] at hly
        exact le_of_mul_le_mul_left (hly.le.trans hcy) (by linarith)) (Real.rpow_nonneg hyp.le (β - 4)))

end HypoellipticAleksandrov.KineticAleksandrov
