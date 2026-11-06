module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.ShiftDifferenceWeights

@[expose] public section
set_option maxHeartbeats 0


                                                                    


open scoped BigOperators
namespace TaoTrudgianYang2025

theorem sum_double_shift_differences (Q R : ℕ) (f : ℤ → ℤ → ℝ) :
    (∑ s ∈ Finset.range Q ×ˢ Finset.range R,
      ∑ t ∈ Finset.range Q ×ˢ Finset.range R, f ((s.1:ℤ)-t.1) ((t.2:ℤ)-s.2)) =
      ∑ q ∈ Finset.Ioo (-(Q:ℤ)) Q, ∑ r ∈ Finset.Ioo (-(R:ℤ)) R,
        ((Q-q.natAbs:ℕ):ℝ)*((R-r.natAbs:ℕ):ℝ)*f q r := by
  calc
    _ = ∑ s ∈ Finset.range Q, ∑ t ∈ Finset.range Q,
        ∑ v ∈ Finset.range R, ∑ u ∈ Finset.range R, f ((s:ℤ)-t) ((v:ℤ)-u) := by
      simp only [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _
      rw [Finset.sum_comm]
    _ = ∑ s ∈ Finset.range Q, ∑ t ∈ Finset.range Q,
        ∑ r ∈ Finset.Ioo (-(R:ℤ)) R, ((R-r.natAbs:ℕ):ℝ)*f ((s:ℤ)-t) r := by
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro t _
      exact sum_signed_shift_differences R (f ((s:ℤ)-t))
    _ = ∑ q ∈ Finset.Ioo (-(Q:ℤ)) Q, ((Q-q.natAbs:ℕ):ℝ)*
        (∑ r ∈ Finset.Ioo (-(R:ℤ)) R, ((R-r.natAbs:ℕ):ℝ)*f q r) :=
      sum_signed_shift_differences Q (fun q =>
        ∑ r ∈ Finset.Ioo (-(R:ℤ)) R, ((R-r.natAbs:ℕ):ℝ)*f q r)
    _ = _ := by
      simp only [Finset.mul_sum,mul_assoc]

theorem signed_shift_weight_real {N : ℕ} {q : ℤ}
    (hq : q ∈ Finset.Ioo (-(N:ℤ)) N) :
    ((N-q.natAbs:ℕ):ℝ) = (N:ℝ)-|(q:ℝ)| := by
  have hqn : q.natAbs ≤ N := by grind
  simp_all


