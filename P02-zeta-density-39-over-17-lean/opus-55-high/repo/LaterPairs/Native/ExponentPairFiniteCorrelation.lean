module
public import GuthMaynard.Weyl
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
import WeylPort.Analytic.RealLaplace

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

 
                                                                

                                                                    
                                                                     


noncomputable section

open Complex Finset
open RiemannZeta.GuthMaynard
open scoped BigOperators

namespace TaoTrudgianYang2025

section
variable (a : ℤ → ℂ) (N H h k : ℕ)
include a N H h k
theorem padded_sequence_correlation_eq
    (hh : h < H) (hk : k < H) (hhk : h < k) :
    (∑ n ∈ Finset.Ico (-(H : ℤ)) N,
      star (paddedShift a N n h)*paddedShift a N n k) =
      ∑ m ∈ Finset.range (N-(k-h)), star (a m)*a (m+(k-h)) := by
  pm_4792
  have hrestrict :
      (∑ n ∈ Finset.Ico (-(H : Int)) N,
        star (if n + (h : Int) ∈ Finset.Ico (0 : Int) N then
          a (n + h) else 0) *
        (if n + (k : Int) ∈ Finset.Ico (0 : Int) N then
          a (n + k) else 0)) =
      ∑ n ∈ s, star (a (n + h)) *
        a (n + k) := by
    pm_4793
    grind
    grind
  rw [hrestrict]
  have hsum :
      (∑ n ∈ s,
        star (a (n + h)) *
          a (n + k)) =
        ∑ m ∈ Finset.range (N - (k - h)),
          star (a m) *
            a (m + (k - h)) := by
    pm_7188
    grind
    grind
    pm_4791
  exact hsum

theorem padded_sequence_correlation_reverse :
    (∑ n ∈ Finset.Ico (-(H : ℤ)) N,
      star (paddedShift a N n h)*paddedShift a N n k) =
    star (∑ n ∈ Finset.Ico (-(H : ℤ)) N,
      star (paddedShift a N n k)*paddedShift a N n h) := by
  pm_7763
  apply Finset.sum_congr rfl
  intro n _
  change star (paddedShift a N n h)*paddedShift a N n k =
    star (star (paddedShift a N n k)*paddedShift a N n h)
  rw [star_mul',star_star]
  ring
end

end TaoTrudgianYang2025
