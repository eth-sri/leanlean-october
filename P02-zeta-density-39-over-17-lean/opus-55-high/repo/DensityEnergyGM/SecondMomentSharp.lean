module
public import DensityEnergyGM.SecondMomentOptimized
public import DensityEnergyGM.SecondMomentPowerAlgebra
import WeylPort.Analytic.RealLaplace

public section

set_option maxHeartbeats 2400000
open Finset GuthMaynard.NativeMoment
namespace Montgomery.RationalMoment

/-- The sharp short-polynomial second-difference moment, with the original
ordered quadruple energy and constants uniform in every polynomial and set. -/
theorem actual_second_moment_sharp_native (ε : ℝ) (hε : 0 < ε) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (M : ℕ) (T : ℝ) (a : ℕ → ℂ) (W : Finset ℝ),
        0 < M → T₀ ≤ T → (M : ℝ) ^ 2 ≤ T →
        (∀ n ∈ Ioc M (2 * M), ‖a n‖ ≤ 1) →
        IsSeparated 1 W → InBaseInterval T W →
        (∑ t ∈ W, ∑ u ∈ W, ‖dirichletPoly M a (t - u)‖ ^ 2) ≤
          C * T ^ ε *
            ((M : ℝ) ^ 2 * (discreteAdditiveEnergy W : ℝ) ^ (1 / 2 : ℝ) +
              (W.card : ℝ) * (discreteAdditiveEnergy W : ℝ) ^ (1 / 4 : ℝ) *
                ((M : ℝ) ^ (9 / 5 : ℝ) +
                  T ^ (1 / 4 : ℝ) * (M : ℝ) ^ (6 / 5 : ℝ))) := by
  pm_4083 C₀ T₀ hC₀ hT₀ hLog actual_second_moment_optimized_log ε hε
  let D : ℝ := (2 : ℝ) ^ (1 / 4 : ℝ)
  let K₁ : ℝ := 2 * C₀ ^ (1 / 4 : ℝ) * (2 : ℝ) ^ (ε / 4) * D
  let K₂ : ℝ := 3 * C₀ ^ (1 / 2 : ℝ) * (2 : ℝ) ^ (ε / 2) / (ε / 2)
  let C : ℝ := K₁ + K₂ + 1
  have hCpos : 0 < C := by dsimp only [C, K₁, K₂, D]; positivity
  pm_505 C T₀ hCpos hT₀
  intro M T a W hM hT hMT ha hSep hBase
  have hTtwo : 2 ≤ T := hT₀.trans hT
  pm_4035
  pm_391 hM0 M
  pm_5014 hE0 discreteAdditiveEnergy W
  by_cases hW : W.Nonempty
  swap
  · have he : W = ∅ := Finset.not_nonempty_iff_eq_empty.mp hW
    subst W
    simp only [Finset.sum_empty]
    positivity
  pm_1116
  pm_7712 C₀
  pm_3947
  let P : ℝ := (M : ℝ) ^ (9 / 5 : ℝ)
  let Z : ℝ := T ^ (1 / 4 : ℝ) * (M : ℝ) ^ (6 / 5 : ℝ)
  have hCzero : 0 ≤ C₀ := by linarith
  pm_82 hK0 K
  pm_82 hB0 B
  have hR0 : 0 ≤ R := Nat.cast_nonneg _
  pm_82 hP0 P
  pm_82 hZ0 Z
  have hD : 1 ≤ D := Real.one_le_rpow (by norm_num) (by norm_num)
  have hBquarter : B ^ (1 / 4 : ℝ) ≤ D * (P + Z) := by
    have h : B ^ (1 / 4 : ℝ) ≤ P + D * Z := by
      simpa only [B, P, D, Z, mul_assoc] using second_moment_quarter_shape hM0 hTpos.le
    nlinarith
  have hKquarter : K ^ (1 / 4 : ℝ) =
      E ^ (1 / 4 : ℝ) * C₀ ^ (1 / 4 : ℝ) *
        (2 : ℝ) ^ (ε / 4) * T ^ (ε / 4) := by
    simpa only [mul_one_div] using
      energy_height_rpow (E := E) (C := C₀) ε (1 / 4) hE0 hCzero hTpos.le
  have hKhalf : Real.sqrt K = E ^ (1 / 2 : ℝ) * C₀ ^ (1 / 2 : ℝ) *
      (2 : ℝ) ^ (ε / 2) * T ^ (ε / 2) := by
    rw [Real.sqrt_eq_rpow]
    simpa only [mul_one_div] using
      energy_height_rpow (E := E) (C := C₀) ε (1 / 2) hE0 hCzero hTpos.le
  have hQuarterPow : T ^ (ε / 4) ≤ T ^ ε :=
    Real.rpow_le_rpow_of_exponent_le hTone (by linarith)
  have hLogPower : T ^ (ε / 2) * Real.log T ≤ T ^ ε / (ε / 2) := by
    have h := Real.log_le_rpow_div hTpos.le (show 0 < ε / 2 by positivity)
    calc
      _ ≤ T ^ (ε / 2) * (T ^ (ε / 2) / (ε / 2)) := by gcongr
      _ = T ^ (ε / 2 + ε / 2) / (ε / 2) := by rw [Real.rpow_add hTpos]; ring
      _ = _ := by congr 2; ring
  have hFirst : 2 * R * Real.sqrt (Real.sqrt K * Real.sqrt B) ≤
      K₁ * T ^ ε * (R * E ^ (1 / 4 : ℝ) * (P + Z)) := by
    rw [geometric_double_sqrt_eq_rpow hK0 hB0, hKquarter]
    calc
      _ ≤ 2 * R *
          ((E ^ (1 / 4 : ℝ) * C₀ ^ (1 / 4 : ℝ) *
            (2 : ℝ) ^ (ε / 4) * T ^ ε) * (D * (P + Z))) := by
        apply mul_le_mul_of_nonneg_left ?_ (by positivity)
        apply mul_le_mul ?_ hBquarter (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left hQuarterPow (by positivity)
      _ = _ := by dsimp only [K₁]; ring
  have hSecond : 3 * Real.sqrt K * (M : ℝ) ^ 2 * Real.log T ≤
      K₂ * T ^ ε * ((M : ℝ) ^ 2 * E ^ (1 / 2 : ℝ)) := by
    rw [hKhalf]
    calc
      _ = (3 * E ^ (1 / 2 : ℝ) * C₀ ^ (1 / 2 : ℝ) *
          (2 : ℝ) ^ (ε / 2) * (M : ℝ) ^ 2) *
            (T ^ (ε / 2) * Real.log T) := by ring
      _ ≤ (3 * E ^ (1 / 2 : ℝ) * C₀ ^ (1 / 2 : ℝ) *
          (2 : ℝ) ^ (ε / 2) * (M : ℝ) ^ 2) * (T ^ ε / (ε / 2)) := by gcongr
      _ = _ := by dsimp only [K₂]; ring
  have h := hLog M T a W hM hT hMT ha hSep hBase hW
  change (∑ t ∈ W, ∑ u ∈ W, ‖dirichletPoly M a (t - u)‖ ^ 2) ≤
    2 * R * Real.sqrt (Real.sqrt K * Real.sqrt B) +
      3 * Real.sqrt K * (M : ℝ) ^ 2 * Real.log T at h
  pm_3988 hK₁zero K₁ D
  pm_82 hK₂zero K₂
  pm_4046 hK₁ K₁ C
  pm_4046 hK₂ K₂ C
  calc
    _ ≤ K₁ * T ^ ε * (R * E ^ (1 / 4 : ℝ) * (P + Z)) +
        K₂ * T ^ ε * ((M : ℝ) ^ 2 * E ^ (1 / 2 : ℝ)) :=
      h.trans (add_le_add hFirst hSecond)
    _ ≤ C * T ^ ε * (R * E ^ (1 / 4 : ℝ) * (P + Z)) +
        C * T ^ ε * ((M : ℝ) ^ 2 * E ^ (1 / 2 : ℝ)) := by gcongr
    _ = _ := by dsimp only [R, E, P, Z]; ring

end Montgomery.RationalMoment
