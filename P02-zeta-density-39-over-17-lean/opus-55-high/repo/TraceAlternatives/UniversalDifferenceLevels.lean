module
public import DensityEnergyGM.DifferencePeaks
public import TraceAlternatives.UniversalSquareLevelCount
import WeylPort.Analytic.RealLaplace

public section

set_option maxHeartbeats 1600000
open Finset GuthMaynard.NativeMoment
namespace Montgomery.RationalMoment

/-- The level count for actual maximizing difference-cell representatives.
The representatives are fixed before the varying level U. Three residue
classes provide genuinely separated ordinates for the native theorem. -/
theorem universal_difference_cell_level_count (ε : ℝ) (hε : 0 < ε) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ (M : ℕ) (T : ℝ) (a : ℕ → ℂ) (W : Finset ℝ),
        0 < M → 2 ≤ T → (M : ℝ) ^ 2 ≤ T →
        (∀ n ∈ Ioc M (2 * M), ‖a n‖ ≤ 1) → InBaseInterval T W →
        ∃ p : ℤ → ℝ × ℝ,
          (∀ j ∈ differenceFloorSupport W,
            p j ∈ differenceOrdinatePairs W ∧ differenceFloor (p j) = j ∧
              ∀ q ∈ differenceOrdinatePairs W, differenceFloor q = j →
                ‖dirichletPoly M a (q.1 - q.2)‖ ≤
                  ‖dirichletPoly M a ((p j).1 - (p j).2)‖) ∧
          ∀ U : ℝ, 0 < U → D*(2*T)^ε*(M:ℝ)^6 ≤ U^8 →
            (((differenceFloorSupport W).filter fun j =>
                U ≤ ‖dirichletPoly M a ((p j).1 - (p j).2)‖).card : ℝ) ≤
              C * (2 * T) ^ ε *
                ((M : ℝ) ^ 4 * U ^ (-4 : ℝ) +
                  (2*T)^(2/3:ℝ)*(M : ℝ) ^ (16 / 3 : ℝ) * U ^ (-8 : ℝ) +
                  (2*T)^(3/5:ℝ)*(M : ℝ) ^ (72 / 5 : ℝ) * U ^ (-96/5 : ℝ)) := by
  classical
  pm_4083 C₀ D hC₀ hD hJ universal_square_level_count ε hε
  pm_6359 D hD
  have hTone : 1 ≤ T := by linarith
  pm_643
  refine ⟨p, hrep, ?_⟩
  intro U hU hCut
  let S := (differenceFloorSupport W).filter fun j =>
    U ≤ ‖dirichletPoly M a ((p j).1 - (p j).2)‖
  let color : ℤ → ℕ := fun j => (j % 3).toNat
  let y : ℤ → ℝ := fun j => (p j).1 - (p j).2 + T
  pm_1538
  have hcolor : ∀ j ∈ S, color j ∈ Finset.range 3 := by
    intro j hj
    pm_5395 hnonneg j
    have hlt := Int.emod_lt_of_pos j (by norm_num : (0 : ℤ) < 3)
    pm_5499 Finset.mem_range
  pm_918
  have hEach : ∀ r ∈ Finset.range 3,
      (((S.filter fun j => color j = r).card) : ℝ) ≤
        C₀ * (2 * T) ^ ε *
          ((M : ℝ) ^ 4 * U ^ (-4 : ℝ) +
            (2*T)^(2/3:ℝ)*(M : ℝ) ^ (16 / 3 : ℝ) * U ^ (-8 : ℝ) +
            (2*T)^(3/5:ℝ)*(M : ℝ) ^ (72 / 5 : ℝ) * U ^ (-96/5 : ℝ)) := by
    intro r hr
    let A := S.filter fun j => color j = r
    let Y := A.image y
    have hA : ∀ j ∈ A, j ∈ S := fun j hj => (Finset.mem_filter.mp hj).1
    pm_367
    have hyinj : Set.InjOn y A := by
      intro i hi j hj heq
      have h := congrArg (fun x : ℝ => ⌊x - T⌋) heq
      rwa [hfloor i hi, hfloor j hj] at h
    have hcardY : Y.card = A.card := Finset.card_image_of_injOn hyinj
    have hSepY : IsSeparated 1 Y := by
      intro x hx z hz hne
      pm_384 i hi Finset.mem_image.mp hx j hj hz
      have hneij : i ≠ j := by intro h; subst j; exact hne rfl
      pm_547 hci Finset.mem_filter.mp hi hcj hj
      have hmod : i % 3 = j % 3 := by
        pm_5395 hinonneg i
        pm_5395 hjnonneg j
        dsimp only [color] at hci hcj
        omega
      have h := difference_floor_residue_separated (hfloor i hi) (hfloor j hj) hmod hneij
      simpa only [Real.dist_eq, sub_sub_sub_cancel_right] using h
    have hBaseY : InBaseInterval (2 * T) Y := by
      pm_136 z hz j hj Finset.mem_image.mp
      have hp := (hrep j (hsupport j (hA j hj))).1
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      have ht := hBase (p j).1 hp1
      have hu := hBase (p j).2 hp2
      dsimp only [y]
      exact ⟨by linarith [ht.1, hu.2], by linarith [ht.2, hu.1]⟩
    have hLargeY : ∀ z ∈ Y,
        U ≤ ‖dirichletPoly M (phaseShiftCoeffs (-T) a) z‖ := by
      pm_136 z hz j hj Finset.mem_image.mp
      pm_1273
    have hcount := hJ M (2 * T) U (phaseShiftCoeffs (-T) a) Y hM
      (by linarith) (by linarith) hU hCut
      (by intro n hn; rw [norm_phaseShiftCoeffs]; exact ha n hn)
      hSepY hBaseY hLargeY
    rw [hcardY] at hcount
    exact hcount
  calc
    (S.card : ℝ) = ∑ r ∈ Finset.range 3,
        (((S.filter fun j => color j = r).card) : ℝ) := by exact_mod_cast hcounts
    _ ≤ ∑ _r ∈ Finset.range 3, C₀ * (2 * T) ^ ε *
        ((M : ℝ) ^ 4 * U ^ (-4 : ℝ) +
          (2*T)^(2/3:ℝ)*(M : ℝ) ^ (16 / 3 : ℝ) * U ^ (-8 : ℝ) +
          (2*T)^(3/5:ℝ)*(M : ℝ) ^ (72 / 5 : ℝ) * U ^ (-96/5 : ℝ)) :=
      Finset.sum_le_sum hEach
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring


end Montgomery.RationalMoment
