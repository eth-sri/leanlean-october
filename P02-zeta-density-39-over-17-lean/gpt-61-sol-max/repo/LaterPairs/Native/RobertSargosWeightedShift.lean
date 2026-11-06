module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.RobertSargosShiftedCorrelation
public import LaterPairs.Native.RobertSargosWeightedBoundary

@[expose] public section
set_option maxHeartbeats 0


                                                                      


open scoped BigOperators
namespace TaoTrudgianYang2025

theorem sum_signed_triangular_double_constant (Q R : ℕ) (hQ : 0 < Q) (hR : 0 < R)
    (C : ℝ) :
    (∑ q ∈ Finset.Ioo (-(Q:ℤ)) Q, ∑ r ∈ Finset.Ioo (-(R:ℤ)) R,
      (1-|(q:ℝ)|/Q)*(1-|(r:ℝ)|/R)*C) = C*Q*R := by
  calc
    _ = C*(∑ q ∈ Finset.Ioo (-(Q:ℤ)) Q, (1-|(q:ℝ)|/Q))*
        (∑ r ∈ Finset.Ioo (-(R:ℤ)) R, (1-|(r:ℝ)|/R)) := by
      simp only [Finset.sum_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
      grind
    _ = _ := by rw [sum_signed_triangular_weights Q hQ,sum_signed_triangular_weights R hR]


