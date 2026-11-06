module
public import DensityEnergyGM.DifferencePeaks
public import DensityEnergyGM.SquaredLevelCount
import WeylPort.Analytic.RealLaplace

public section

set_option maxHeartbeats 1600000
open Finset GuthMaynard.NativeMoment
namespace Montgomery.RationalMoment

section
variable (ε : ℝ) (hε : 0 < ε)
include ε hε
/-- The level count for actual maximizing difference-cell representatives.
The representatives are fixed before the varying level U. Three residue
classes provide genuinely separated ordinates for the native theorem. -/
theorem difference_cell_level_count_native :
    ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
      ∀ (M : ℕ) (T : ℝ) (a : ℕ → ℂ) (W : Finset ℝ),
        0 < M → T₀ ≤ T → (M : ℝ) ^ 2 ≤ T →
        (∀ n ∈ Ioc M (2 * M), ‖a n‖ ≤ 1) → InBaseInterval T W →
        ∃ p : ℤ → ℝ × ℝ,
          (∀ j ∈ differenceFloorSupport W,
            p j ∈ differenceOrdinatePairs W ∧ differenceFloor (p j) = j ∧
              ∀ q ∈ differenceOrdinatePairs W, differenceFloor q = j →
                ‖dirichletPoly M a (q.1 - q.2)‖ ≤
                  ‖dirichletPoly M a ((p j).1 - (p j).2)‖) ∧
          ∀ U : ℝ, 0 < U →
            (((differenceFloorSupport W).filter fun j =>
                U ≤ ‖dirichletPoly M a ((p j).1 - (p j).2)‖).card : ℝ) ≤
              C * (2 * T) ^ ε *
                ((M : ℝ) ^ 4 * U ^ (-4 : ℝ) +
                  (M : ℝ) ^ (36 / 5 : ℝ) * U ^ (-8 : ℝ) +
                  (2 * T) * (M : ℝ) ^ (24 / 5 : ℝ) * U ^ (-8 : ℝ)) := by
  classical
  pm_4083 C₀ T₀ hC₀ hT₀ hJ squared_polynomial_level_count_native ε hε
  pm_6359 T₀ hT₀
  have hTone : 1 ≤ T := hT₀.trans hT
  pm_643
  pm_4114 S
  pm_4112
  pm_1538
  have hcolor : ∀ j ∈ S, color j ∈ Finset.range 3 := by
    pm_4113
    pm_5499 Finset.mem_range
  pm_918
  have hEach : ∀ r ∈ Finset.range 3,
      (((S.filter fun j => color j = r).card) : ℝ) ≤
        C₀ * (2 * T) ^ ε *
          ((M : ℝ) ^ 4 * U ^ (-4 : ℝ) +
            (M : ℝ) ^ (36 / 5 : ℝ) * U ^ (-8 : ℝ) +
            (2 * T) * (M : ℝ) ^ (24 / 5 : ℝ) * U ^ (-8 : ℝ)) := by
    pm_4111
    pm_367
    pm_4110
    have hcardY : Y.card = A.card := Finset.card_image_of_injOn hyinj
    pm_4109
    have hLargeY : ∀ z ∈ Y,
        U ≤ ‖dirichletPoly M (phaseShiftCoeffs (-T) a) z‖ := by
      pm_136 z hz j hj Finset.mem_image.mp
      pm_1273
    have hcount := hJ M (2 * T) U (phaseShiftCoeffs (-T) a) Y hM
      (by linarith) (by linarith) hU
      (by intro n hn; rw [norm_phaseShiftCoeffs]; exact ha n hn)
      hSepY hBaseY hLargeY
    rw [hcardY] at hcount
    exact hcount
  calc
    (S.card : ℝ) = ∑ r ∈ Finset.range 3,
        (((S.filter fun j => color j = r).card) : ℝ) := by exact_mod_cast hcounts
    _ ≤ ∑ _r ∈ Finset.range 3, C₀ * (2 * T) ^ ε *
        ((M : ℝ) ^ 4 * U ^ (-4 : ℝ) +
          (M : ℝ) ^ (36 / 5 : ℝ) * U ^ (-8 : ℝ) +
          (2 * T) * (M : ℝ) ^ (24 / 5 : ℝ) * U ^ (-8 : ℝ)) :=
      Finset.sum_le_sum hEach
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- The weighted weak level estimate used in the sharper second moment.
Every weight is the literal number of original pairs in a unit difference
cell; the same representatives work for every positive threshold. -/
theorem difference_cell_weighted_level_native :
    ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
      ∀ (M : ℕ) (T : ℝ) (a : ℕ → ℂ) (W : Finset ℝ),
        0 < M → T₀ ≤ T → (M : ℝ) ^ 2 ≤ T →
        (∀ n ∈ Ioc M (2 * M), ‖a n‖ ≤ 1) → InBaseInterval T W →
        ∃ p : ℤ → ℝ × ℝ,
          (∀ j ∈ differenceFloorSupport W,
            p j ∈ differenceOrdinatePairs W ∧ differenceFloor (p j) = j ∧
              ∀ q ∈ differenceOrdinatePairs W, differenceFloor q = j →
                ‖dirichletPoly M a (q.1 - q.2)‖ ≤
                  ‖dirichletPoly M a ((p j).1 - (p j).2)‖) ∧
          ∀ U : ℝ, 0 < U →
            (∑ j ∈ (differenceFloorSupport W).filter (fun j =>
                U ≤ ‖dirichletPoly M a ((p j).1 - (p j).2)‖),
                (differenceFloorCount W j : ℝ)) ≤
              min ((W.card : ℝ) ^ 2)
                (Real.sqrt ((discreteAdditiveEnergy W : ℝ) *
                  (C * (2 * T) ^ ε *
                    ((M : ℝ) ^ 4 * U ^ (-4 : ℝ) +
                      (M : ℝ) ^ (36 / 5 : ℝ) * U ^ (-8 : ℝ) +
                      (2 * T) * (M : ℝ) ^ (24 / 5 : ℝ) * U ^ (-8 : ℝ))))) := by
  pm_4083 C T₀ hC hT₀ hLevels difference_cell_level_count_native ε hε
  pm_4084
  pm_5583 hcounts hLevels
  pm_4114 J
  let B : ℝ := C * (2 * T) ^ ε *
    ((M : ℝ) ^ 4 * U ^ (-4 : ℝ) +
      (M : ℝ) ^ (36 / 5 : ℝ) * U ^ (-8 : ℝ) +
      (2 * T) * (M : ℝ) ^ (24 / 5 : ℝ) * U ^ (-8 : ℝ))
  let mass : ℝ := ∑ j ∈ J, (differenceFloorCount W j : ℝ)
  have hsub : J ⊆ differenceFloorSupport W := Finset.filter_subset _ _
  have hmass0 : 0 ≤ mass := Finset.sum_nonneg fun j hj => Nat.cast_nonneg _
  pm_5014 hE0 discreteAdditiveEnergy W
  pm_485 hTpos T lt_of_lt_of_le zero_lt_one hT₀.trans hT
  pm_82 hB0 B
  have hcard : (J.card : ℝ) ≤ B := hcounts U hU
  have hmassSq : mass ^ 2 ≤ (discreteAdditiveEnergy W : ℝ) * B := by
    have h := differenceFloor_subset_mass_sq W J hsub
    have hc := mul_le_mul_of_nonneg_right hcard hE0
    dsimp only [mass]
    nlinarith
  have hRoot : mass ≤ Real.sqrt ((discreteAdditiveEnergy W : ℝ) * B) := by
    have hs := Real.sq_sqrt (mul_nonneg hE0 hB0)
    have hsn := Real.sqrt_nonneg ((discreteAdditiveEnergy W : ℝ) * B)
    nlinarith
  have htotal : (∑ j ∈ differenceFloorSupport W,
      (differenceFloorCount W j : ℝ)) = (W.card : ℝ) ^ 2 := by
    exact_mod_cast sum_differenceFloorCount W
  have hTrivial : mass ≤ (W.card : ℝ) ^ 2 := by
    rw [← htotal]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun j hj hnot => Nat.cast_nonneg _)
  exact le_min hTrivial hRoot
end

end Montgomery.RationalMoment
