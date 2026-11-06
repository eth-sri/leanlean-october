module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.LeakageVolume
import Mathlib.Tactic
import Batteries.Tactic.Alias
import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabFourierMarginal



/-! # Dimension-only constants and error absorption for ink spots -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.InkSpots

open Set MeasureTheory Covering

variable (d : ℕ)

/-- Proportional gain from factor-eight kinetic selection. -/
def coveringGain  : ℝ := ((8 : ℝ)^(4*d+2))⁻¹

/-- A single dimension-only constant absorbs both spatial and delayed leakage shells. -/
def coveringLeakage  : ℝ :=
  (32+4*(5 : ℝ)^d+4*(d : ℝ))*(volume (unitCylinder d)).toReal

/-- The gain is positive and no larger than one half. -/
theorem coveringGain_bounds  : 0 < coveringGain d ∧ coveringGain d ≤ 1/2 := by
  have hB : 2 ≤ (8 : ℝ)^(4*d+2) := by
    rw [pow_add]
    have h := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 8) (n := 4*d)
    norm_num
    nlinarith

  have heq : coveringGain d*(8 : ℝ)^(4*d+2) = 1 := inv_mul_cancel₀ (by positivity)
  exact ⟨(inv_pos.mpr (by positivity)), by nlinarith⟩

/-- The leakage constant is positive and at least 32 times unit volume. -/
theorem coveringLeakage_bounds  : 0 < coveringLeakage d ∧
    32*(volume (unitCylinder d)).toReal ≤ coveringLeakage d := by
  have hV : 0 < (volume (unitCylinder d)).toReal := ENNReal.toReal_pos
    (volume_cylinder_pos_ne_top _ zero_lt_one).1.ne'
    (volume_cylinder_pos_ne_top _ zero_lt_one).2

  have hk : 0 ≤ (5 : ℝ)^d := by positivity
  dsimp [coveringLeakage]
  constructor <;> nlinarith

/-- The delayed multiplier is at least one for every positive natural height. -/
theorem delay_multiplier_ge_one {m : ℕ} (hm : 0 < m) :
    1 ≤ ((m : ℝ)+1)/(m : ℝ) := (Green.one_le_slabGamma0 hm)


/-- A positive threshold leaves at least half of the multiplicative density factor. -/
theorem density_factor_bounds (d : ℕ) {eta : ℝ} (heta : 0 < eta) (heta1 : eta < 1) :
    1/2 ≤ 1-coveringGain d*eta ∧ 1-coveringGain d*eta ≤ 1 := by
  obtain ⟨hc, hc1⟩ := coveringGain_bounds d
  constructor <;> nlinarith

/-- The two small-height errors fit inside the chosen final leakage constant. -/
theorem absorb_covering_errors {e f V k n a q h s : ℝ}
    (hV : 0 ≤ V) (hk : 0 ≤ k) (hn : 0 ≤ n) (ha : 1/2 ≤ a) (hq : 1 ≤ q)
    (hh : 0 ≤ h) (hs : s ≤ h)
    (he : e ≤ a*q*(f+2*k*V*h)+2*n*V*s) :
    e ≤ q*a*(f+(32+4*k+4*n)*V*h) := by
  let sharedTerm_a369b9ee51 := ((32 + 4 * k + 4 * n) * V - 2 * k * V)



  have herr : 2*n*V*s ≤ q*a*((sharedTerm_a369b9ee51)*h) := by
    calc
      _ ≤ 2*n*V*h := mul_le_mul_of_nonneg_left hs (by positivity)
      _ ≤ (1/2)*((sharedTerm_a369b9ee51)*h) := by
        nlinarith only [mul_le_mul_of_nonneg_right (show 2*n*V ≤ (1/2)*(sharedTerm_a369b9ee51) by nlinarith) hh]
      _ ≤ _ := mul_le_mul_of_nonneg_right (show 1/2 ≤ q*a by nlinarith) (mul_nonneg (show 0 ≤ sharedTerm_a369b9ee51 by nlinarith) hh)
  nlinarith only [he, herr]

/-- When the error height is at least 1/16 the desired upper bound is already unit volume. -/
theorem trivial_large_height {V f C q a h : ℝ} (hV : 0 ≤ V) (hf : 0 ≤ f)
    (hC : 32*V ≤ C) (hq : 1 ≤ q) (ha : 1/2 ≤ a) (hh : 1/16 ≤ h) :
    V ≤ q*a*(f+C*h) := by


  have hCh : 2*V ≤ C*h := by
    have h := mul_le_mul_of_nonneg_left hh (by linarith)
    nlinarith

  have h := mul_le_mul_of_nonneg_right (show 1/2 ≤ q*a by nlinarith) (show 0 ≤ f+C*h by nlinarith)
  nlinarith

end HypoellipticAleksandrov.KineticAleksandrov.Holder.InkSpots
