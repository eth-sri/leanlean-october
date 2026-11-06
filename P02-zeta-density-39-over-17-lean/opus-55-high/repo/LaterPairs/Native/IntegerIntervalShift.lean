module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.IntegerIntervalBoundary
import WeylPort.Analytic.RealLaplace

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                                      

noncomputable section
open scoped BigOperators
namespace TaoTrudgianYang2025

theorem sum_integer_interval_translate (w : ℤ → ℂ) (a b n : ℤ) :
    (∑ m ∈ Finset.Icc (a-n) (b-n), w (m+n)) = ∑ m ∈ Finset.Icc a b, w m := by
  pm_8905 n
  grind
  grind
  · intro m hm
    refine ⟨m-n,?_,by omega⟩
    simp only [Finset.mem_Icc] at hm ⊢
    grind
  grind

theorem sum_integer_interval_average (w : ℤ → ℂ) (a b : ℤ) (N : ℕ) (hN : 0 < N) :
    (∑ m ∈ Finset.Icc a b, w m) =
      (N:ℂ)⁻¹*∑ n ∈ Finset.Icc (1:ℤ) N,
        ∑ m ∈ Finset.Icc (a-n) (b-n), w (m+n) := by
  simp_rw [sum_integer_interval_translate]
  pm_1385
  simp only [Finset.sum_const,hc,nsmul_eq_mul]
  have hn : (N:ℂ) ≠ 0 := by aesop
  grind

end TaoTrudgianYang2025
