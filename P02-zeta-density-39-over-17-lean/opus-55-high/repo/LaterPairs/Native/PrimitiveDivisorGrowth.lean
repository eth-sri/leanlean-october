module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import GuthMaynard.AffineSource.Foundation
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.PrimitiveTripleCount
import WeylPort.Analytic.RealLaplace

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                                     

noncomputable section
namespace TaoTrudgianYang2025

theorem sum_divisors_cast_le_mul_card (n : ℕ) :
    (∑ g ∈ n.divisors, (g:ℝ)) ≤ (n:ℝ)*(n.divisors.card:ℝ) := by
  calc
    _ ≤ ∑ _g ∈ n.divisors, (n:ℝ) := by
      apply Finset.sum_le_sum
      intro g hg
      exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hg).2)
        (Nat.dvd_of_mem_divisors hg)
    _ = _ := by simp [mul_comm]

theorem exists_primitive_divisor_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (K : ℝ), 0 < n → 0 ≤ K →
      (n.divisors.card:ℝ)+K/(n:ℝ)^2*(∑ g ∈ n.divisors, (g:ℝ)) ≤
        C*(n:ℝ)^ε*(1+K/n) := by
  pm_1657 C hC hdiv RiemannZeta.GuthMaynard.divisorCountBound_native ε hε
  intro n K hn hK
  pm_4473 hnr n hn
  calc
    _ ≤ (n.divisors.card:ℝ)+K/(n:ℝ)^2*((n:ℝ)*(n.divisors.card:ℝ)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (sum_divisors_cast_le_mul_card n)
        (by positivity : 0 ≤ K/(n:ℝ)^2))
    _ = (n.divisors.card:ℝ)*(1+K/n) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (hdiv n hn) (by positivity)

end TaoTrudgianYang2025
