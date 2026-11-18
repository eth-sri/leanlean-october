module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionCells
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionPowerSum
import Mathlib.Tactic
import Mathlib.Algebra.Order.Floor.Ring

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory


/-- Extended real masses of all position cells sum to the time-bin mass. -/
theorem tsum_ofReal_enlargedPositionVisitMass (nu : Measure Point) [IsFiniteMeasure nu]
    (c : Clock) (s x : ℝ) (j : ℕ) :
    (∑' k : ℤ, ENNReal.ofReal (enlargedPositionVisitMass nu c s x j k)) =
      ENNReal.ofReal (enlargedTimeVisitMass nu c s j) := by
  unfold enlargedPositionVisitMass enlargedTimeVisitMass
  simp_rw [ENNReal.ofReal_toReal (measure_ne_top nu _)]
  exact tsum_enlargedPositionVisitCell_measure nu c s x j




/-- A visit cell beyond the supported time horizon has zero mass. -/
theorem enlargedPositionVisitMass_eq_zero_of_horizon
    (nu : Measure Point) (c : Clock) (s x T : ℝ) (j : ℕ) (k : ℤ)
    (hs : ∀ᵐ p ∂nu, p.time < s + T) (hj : T ≤ (j : ℝ) * c.r ^ 2) :
    enlargedPositionVisitMass nu c s x j k = 0 := by
  have hz : nu (enlargedStartCell c s x j k ∩
      {p | p.velocity 0 ∈ closure c.entrance}) = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    apply hs.mono
    intro p hp hcell
    have hl := (enlargedTimeBin_bounds c.r s p.time j hcell.1.1).1
    linarith
  unfold enlargedPositionVisitMass
  rw [hz, ENNReal.toReal_zero]

/-- The source double q-power sum follows from the literal time and cell counts.
This helper is applied only after its two decay premises are proved for the same measure. -/
theorem enlargedPositionVisitMass_power_sum_horizon_le
    (nu : Measure Point) [IsFiniteMeasure nu] (c : Clock) (s x R T : ℝ)
    (hR : 0 < R) (hT : 0 < T) (hTR : T ≤ R ^ 2)
    (hs : ∀ᵐ p ∂nu, p.time < s + T)
    (Ct Cp g q : ℝ) (hCt : 0 ≤ Ct) (hCp : 0 ≤ Cp)
    (hg : 1 < g ∧ g < 2) (hq : 1 < q ∧ q < 3 / 2)
    (htime : ∀ j : ℕ,
      enlargedTimeVisitMass nu c s j ≤ Ct * (1 + (j : ℝ)) ^ (-1 / 2 : ℝ))
    (hcell : ∀ (j : ℕ) (k : ℤ),
      enlargedPositionVisitMass nu c s x j k ≤ Cp * (1 + (j : ℝ)) ^ (-g / 2)) :
    (∑' j : ℕ, ∑' k : ℤ, ENNReal.ofReal (enlargedPositionVisitMass nu c s x j k ^ q)) ≤
      ENNReal.ofReal ((Cp ^ (q - 1) * Ct *
        ((1 + 1 / (1 - (1 + g * (q - 1)) / 2)) *
          (3 : ℝ) ^ (1 - (1 + g * (q - 1)) / 2))) *
            (1 + R / c.r) ^ (1 - g * (q - 1)))  := by
  have enlargedPositionVisitMass_power_sum_decay_le [IsFiniteMeasure nu] (j : ℕ) (_hCt : 0 ≤ Ct) (hq : 1 < q) (htime : enlargedTimeVisitMass nu c s j ≤ Ct * (1 + (j : ℝ)) ^ (-1 / 2 : ℝ)) (hcell : ∀ k : ℤ,
      enlargedPositionVisitMass nu c s x j k ≤ Cp * (1 + (j : ℝ)) ^ (-g / 2)) :
      (∑' k : ℤ, ENNReal.ofReal (enlargedPositionVisitMass nu c s x j k ^ q)) ≤
      ENNReal.ofReal (Cp ^ (q - 1) * Ct *
        (1 + (j : ℝ)) ^ (-(1 + g * (q - 1)) / 2)) := by
    have enlargedPositionVisitMass_power_sum_le [IsFiniteMeasure nu] (M : ℝ) (hM : 0 ≤ M) (hcell : ∀ k : ℤ, enlargedPositionVisitMass nu c s x j k ≤ M) :
        (∑' k : ℤ, ENNReal.ofReal (enlargedPositionVisitMass nu c s x j k ^ q)) ≤
        ENNReal.ofReal (M ^ (q - 1) * enlargedTimeVisitMass nu c s j) := by
      have position_mass_rpow_le {x : ℝ} {M : ℝ} (hx : 0 ≤ x) (hM : x ≤ M) :
          x ^ q ≤ M ^ (q - 1) * x := by
        calc
          x ^ q = x ^ (q - 1) * x := by
            calc
              _ = x ^ ((q - 1) + 1) := by congr 1; ring
              _ = _ := by
                rw [Real.rpow_add_of_nonneg hx (by linarith : 0 ≤ q - 1) zero_le_one,
                  Real.rpow_one]
          _ ≤ M ^ (q - 1) * x := mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow hx hM (by linarith)) hx
      have hn : ∀ k : ℤ, 0 ≤ enlargedPositionVisitMass nu c s x j k :=
        fun _ => ENNReal.toReal_nonneg
      calc
        _ ≤ ∑' k : ℤ, ENNReal.ofReal
            (M ^ (q - 1) * enlargedPositionVisitMass nu c s x j k) :=
          ENNReal.tsum_le_tsum fun k => ENNReal.ofReal_le_ofReal
            (position_mass_rpow_le (hn k) (hcell k))
        _ = ENNReal.ofReal (M ^ (q - 1)) *
            ∑' k : ℤ, ENNReal.ofReal (enlargedPositionVisitMass nu c s x j k) := by
          simp_rw [ENNReal.ofReal_mul (Real.rpow_nonneg hM _)]
          exact ENNReal.tsum_mul_left
        _ = _ := by
          rw [tsum_ofReal_enlargedPositionVisitMass,
            ← ENNReal.ofReal_mul (Real.rpow_nonneg hM _)]
    have hp : 0 < 1 + (j : ℝ) := by positivity
    apply (enlargedPositionVisitMass_power_sum_le
      (Cp * (1 + (j : ℝ)) ^ (-g / 2))
        (mul_nonneg hCp (Real.rpow_nonneg hp.le _)) hcell).trans
    apply ENNReal.ofReal_le_ofReal
    have h := mul_le_mul_of_nonneg_left htime
      (Real.rpow_nonneg (mul_nonneg hCp (Real.rpow_nonneg hp.le (-g / 2))) (q - 1))
    apply h.trans_eq
    rw [Real.mul_rpow hCp (Real.rpow_nonneg hp.le _), ← Real.rpow_mul hp.le]
    calc
      _ = Cp ^ (q - 1) * Ct *
          ((1 + (j : ℝ)) ^ ((-g / 2) * (q - 1)) *
            (1 + (j : ℝ)) ^ (-1 / 2 : ℝ)) := by ring
      _ = _ := by
        rw [← Real.rpow_add hp]
        congr 2
        ring
  let N : ℕ := ⌊T / c.r ^ 2⌋₊ + 1
  have hr := c.positive
  have hr2 := sq_pos_of_pos hr
  have hNlo : T / c.r ^ 2 < (N : ℝ) := by
    simpa only [N, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (T / c.r ^ 2)
  have hNhi : (N : ℝ) ≤ T / c.r ^ 2 + 1 := by
    have h := Nat.floor_le (by positivity : 0 ≤ T / c.r ^ 2)
    simp only [N, Nat.cast_add, Nat.cast_one]
    linarith
  have hNhorizon : (N : ℝ) ≤ 2 + (R / c.r) ^ 2 := by
    have ht := div_le_div_of_nonneg_right hTR hr2.le
    rw [div_pow] at ⊢
    linarith
  have hz : ∀ j : ℕ, j ∉ Finset.range (N + 1) →
      (∑' k : ℤ, ENNReal.ofReal (enlargedPositionVisitMass nu c s x j k ^ q)) = 0 := by
    intro j hj
    have hjN : N ≤ j := by
      simp at hj
      omega
    have hcast : (N : ℝ) ≤ (j : ℝ) := by exact_mod_cast hjN
    have htj : T ≤ (j : ℝ) * c.r ^ 2 := by
      have h := (div_lt_iff₀ hr2).mp hNlo
      exact h.le.trans (mul_le_mul_of_nonneg_right hcast hr2.le)
    have he : ∀ k : ℤ, enlargedPositionVisitMass nu c s x j k = 0 :=
      fun k => enlargedPositionVisitMass_eq_zero_of_horizon nu c s x T j k hs htj
    simp [he, Real.zero_rpow (by linarith [hq.1] : q ≠ 0), tsum_zero]
  rw [tsum_eq_sum hz]
  apply (Finset.sum_le_sum (fun j _ =>
    enlargedPositionVisitMass_power_sum_decay_le j hCt
      hq.1 (htime j) (hcell j))).trans
  have hcoef : 0 ≤ Cp ^ (q - 1) * Ct := mul_nonneg (Real.rpow_nonneg hCp _) hCt
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ =>
    mul_nonneg hcoef (Real.rpow_nonneg (by positivity) _)), ← Finset.mul_sum]
  apply ENNReal.ofReal_le_ofReal
  exact (mul_le_mul_of_nonneg_left (position_decay_power_sum_horizon_le g q hg hq R c.r hR.le hr N hNhorizon) hcoef).trans_eq (mul_assoc _ _ _).symm

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

