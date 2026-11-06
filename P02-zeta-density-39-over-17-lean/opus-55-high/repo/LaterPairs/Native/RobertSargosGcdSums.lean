module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.RobertSargosDisplacementSums
import WeylPort.Analytic.RealLaplace

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                               

noncomputable section
namespace TaoTrudgianYang2025

theorem sum_inverse_gcd_product (J K : ℕ) :
    (∑ j ∈ Finset.Icc 1 J, ∑ k ∈ Finset.Icc 1 K, (1:ℝ)/((j:ℝ)*(k:ℝ))) =
      (harmonic J:ℝ)*(harmonic K:ℝ) := by
  simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
  rw [Finset.sum_mul_sum]
  pm_156 Finset.sum_congr j k
  grind

theorem exists_robertSargos_gcd_harmonic_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ R H Q : ℝ, 1 ≤ R → 1 ≤ H → 1 ≤ Q →
      (harmonic ⌊R⌋₊:ℝ)*(harmonic ⌊2*Q⌋₊:ℝ) ≤ C*(R*H*Q)^ε := by
  let η := ε/2
  let K := 1+1/η
  pm_358 hη η
  pm_64 hK K
  pm_7932 K η
  intro R H Q hR hH hQ
  pm_72 hRp R hHp H
  have hQp : 0 < Q := by linarith
  pm_655 hB R H Q
  have hRB : R ≤ R*H*Q :=
    (le_mul_of_one_le_right hRp.le hH).trans
      (le_mul_of_one_le_right (by positivity : 0 ≤ R*H) hQ)
  have hQB : Q ≤ R*H*Q := by
    have hm := mul_le_mul_of_nonneg_right
      (one_le_mul_of_one_le_of_one_le hR hH) hQp.le
    grind
  have hJ : 1 ≤ ⌊R⌋₊ := (Nat.one_le_floor_iff R).mpr hR
  have hL : 1 ≤ ⌊2*Q⌋₊ := (Nat.one_le_floor_iff (2*Q)).mpr (by linarith)
  have hJbound : (⌊R⌋₊:ℝ) ≤ R*H*Q := (Nat.floor_le hRp.le).trans hRB
  have hLbound : (⌊2*Q⌋₊:ℝ) ≤ 2*(R*H*Q) :=
    (Nat.floor_le (by positivity : 0 ≤ 2*Q)).trans
      (mul_le_mul_of_nonneg_left hQB (by norm_num))
  have hfirst : (harmonic ⌊R⌋₊:ℝ) ≤ K*(R*H*Q)^η :=
    (harmonic_le_rpow_loss η hη hJ).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) hJbound hη.le) hK.le)
  have hsecond : (harmonic ⌊2*Q⌋₊:ℝ) ≤ K*(2*(R*H*Q))^η :=
    (harmonic_le_rpow_loss η hη hL).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) hLbound hη.le) hK.le)
  have hsq : (R*H*Q)^η*(R*H*Q)^η = (R*H*Q)^ε := by
    rw [← Real.rpow_add hB]
    congr 1
    dsimp [η]
    ring
  calc
    _ ≤ (K*(R*H*Q)^η)*(K*(2*(R*H*Q))^η) :=
      mul_le_mul hfirst hsecond
        (by
          simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
          exact Finset.sum_nonneg (fun _ _ => by positivity)) (by positivity)
    _ = K^2*(2:ℝ)^η*((R*H*Q)^η*(R*H*Q)^η) := by
      pm_7402 hB.le
      ring
    _ = _ := by rw [hsq]

end TaoTrudgianYang2025
