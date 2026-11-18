module
public import DensityEnergyGM.BasicPairSecondEnergy

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Finset
namespace Montgomery.RationalMoment

/-- Absorb the literal gcd logarithm at any fixed polynomial height. -/
theorem polynomial_height_log_loss (B δ : ℝ) (hB : 0 < B) (hδ : 0 < δ)
    {T X : ℝ} (hT : 1 ≤ T) (hX : 0 < X) (hXT : X ≤ T ^ B) :
    1 + Real.log ⌊2 * X⌋₊ ≤
      (1 + (2 : ℝ) ^ (δ / B) / (δ / B)) * T ^ δ := by
  have hTp : 0 < T := by linarith
  have hq : 0 < δ / B := div_pos hδ hB
  have hOne : 1 ≤ T ^ δ := Real.one_le_rpow hT hδ.le
  have hFloor : (⌊2 * X⌋₊ : ℝ) ≤ 2 * T ^ B :=
    (Nat.floor_le (by positivity)).trans (by gcongr)
  have hLog : Real.log ⌊2 * X⌋₊ ≤
      ((2 : ℝ) ^ (δ / B) * T ^ δ) / (δ / B) := by
    calc
      _ ≤ (⌊2 * X⌋₊ : ℝ) ^ (δ / B) / (δ / B) :=
        Real.log_natCast_le_rpow_div _ hq
      _ ≤ (2 * T ^ B) ^ (δ / B) / (δ / B) := by gcongr
      _ = _ := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity),
          ← Real.rpow_mul hTp.le]
        congr 3
        field_simp
  calc
    _ ≤ T ^ δ + ((2 : ℝ) ^ (δ / B) * T ^ δ) / (δ / B) := add_le_add hOne hLog
    _ = _ := by ring

end Montgomery.RationalMoment
