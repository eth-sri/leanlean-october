module
public import TraceAlternatives.CubeMoment
public import DensityEnergyGM.DifferenceLayerCake
import WeylPort.Analytic.RealLaplace

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Finset GuthMaynard.NativeMoment
namespace Montgomery.RationalMoment

/-- The actual cell representatives, partitioned into three separated
classes, obey the sixth-moment estimate. W itself need not be separated. -/
theorem difference_peak_sixth_moment_native (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ℕ) (T : ℝ) (a : ℕ → ℂ) (W : Finset ℝ),
        0 < M → 2 ≤ T → (M : ℝ) ^ 2 ≤ T →
        (∀ n ∈ Ioc M (2 * M), ‖a n‖ ≤ 1) → InBaseInterval T W →
        ∀ p : ℤ → ℝ × ℝ,
          (∀ j ∈ differenceFloorSupport W,
            p j ∈ differenceOrdinatePairs W ∧ differenceFloor (p j) = j) →
          (∑ j ∈ differenceFloorSupport W,
            ‖dirichletPoly M a ((p j).1 - (p j).2)‖ ^ 6) ≤
              C * T ^ ε * ((M : ℝ) ^ 6 + T * (M : ℝ) ^ 3) := by
  classical
  pm_98 C₀ hC₀ hMoment short_polynomial_sixth_moment_native ε hε
  refine ⟨6 * C₀ * (2 : ℝ) ^ ε, by positivity, ?_⟩
  intro M T a W hM hT hMT ha hBase p hrep
  have hTp : 0 < T := by linarith
  let S := differenceFloorSupport W
  pm_4112
  have hsupport : ∀ j ∈ S, j ∈ differenceFloorSupport W := fun _ h => h
  have hcolor : ∀ j ∈ S, color j ∈ range 3 := by
    pm_4113
    pm_5499 mem_range
  have hEach : ∀ r ∈ range 3,
      (∑ j ∈ S.filter (fun j => color j = r),
        ‖dirichletPoly M a ((p j).1 - (p j).2)‖ ^ 6) ≤
          C₀ * (2 * T) ^ ε * ((M : ℝ) ^ 6 + (2 * T) * (M : ℝ) ^ 3) := by
    pm_4111
    have hfloor : ∀ j ∈ A, ⌊y j - T⌋ = j := by
      intro j hj
      have h := (hrep j (hsupport j (hA j hj))).2
      simpa only [y, add_sub_cancel_right, differenceFloor] using h
    pm_4110
    pm_4109
    have hh := hMoment M (2 * T) (phaseShiftCoeffs (-T) a) Y hM
      (by linarith) (by linarith)
      (by intro n hn; rw [norm_phaseShiftCoeffs]; exact ha n hn) hSepY hBaseY
    have hSum : (∑ z ∈ Y, ‖dirichletPoly M (phaseShiftCoeffs (-T) a) z‖ ^ 6) =
        ∑ j ∈ A, ‖dirichletPoly M a ((p j).1 - (p j).2)‖ ^ 6 := by
      rw [sum_image hyinj]
      apply sum_congr rfl
      intro j hj
      dsimp only [y]
      rw [← dirichletPoly_difference_eq_translated]
    rw [hSum] at hh
    exact hh
  have hPartition : (∑ j ∈ S, ‖dirichletPoly M a ((p j).1 - (p j).2)‖ ^ 6) =
      ∑ r ∈ range 3, ∑ j ∈ S.filter (fun j => color j = r),
        ‖dirichletPoly M a ((p j).1 - (p j).2)‖ ^ 6 :=
    (sum_fiberwise_of_maps_to hcolor _).symm
  calc
    _ = _ := hPartition
    _ ≤ ∑ _r ∈ range 3, C₀ * (2 * T) ^ ε *
        ((M : ℝ) ^ 6 + (2 * T) * (M : ℝ) ^ 3) := sum_le_sum hEach
    _ = 3 * C₀ * (2 : ℝ) ^ ε * T ^ ε *
        ((M : ℝ) ^ 6 + (2 * T) * (M : ℝ) ^ 3) := by
      simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_ofNat]
      rw [Real.mul_rpow (by norm_num) hTp.le]
      ring
    _ ≤ _ := by
      have hh : 0 ≤ C₀ * (2 : ℝ) ^ ε * T ^ ε * (M : ℝ) ^ 6 := by positivity
      nlinarith

end Montgomery.RationalMoment
