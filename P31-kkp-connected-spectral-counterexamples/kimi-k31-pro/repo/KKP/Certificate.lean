module
public import Mathlib
public section

namespace CounterexampleCertificate

theorem denominator_pos (s : ℝ) (hs : 3 ≤ s) : 0 < 37 * s - 1 := by linarith

theorem compression_determinant_pos (s : ℝ) (hs : 3 ≤ s) :
    0 < 2 * s * ((114 * s - 6) / (37 * s - 1)) - 3 / (37 * s - 1) := by
  have hd := denominator_pos s hs
  have hn : 0 < 228 * s ^ 2 - 12 * s - 3 := by
    nlinarith [sq_nonneg (s - 3),
      mul_nonneg (sub_nonneg.mpr hs) (by norm_num : (0 : ℝ) ≤ 1356)]
  rw [show 2 * s * ((114 * s - 6) / (37 * s - 1)) - 3 / (37 * s - 1) =
    (228 * s ^ 2 - 12 * s - 3) / (37 * s - 1) by field_simp; ring]
  exact div_pos hn hd

theorem excess_numerator_pos (s : ℝ) (hs : 3 ≤ s) :
    0 < 656 * s ^ 2 - 1366 * s + 62 := by
  nlinarith [sq_nonneg (s - 3),
    mul_nonneg (sub_nonneg.mpr hs) (by norm_num : (0 : ℝ) ≤ 2570)]

theorem compression_gap_identity (s : ℝ) (hd : 37 * s - 1 ≠ 0) :
    (4 * s ^ 2 + ((114 * s - 6) / (37 * s - 1)) ^ 2 +
      6 / (37 * s - 1)) - (4 / 3 : ℝ) * (3 * s ^ 2 + 7) =
    (656 * s ^ 2 - 1366 * s + 62) / (3 * (37 * s - 1) ^ 2) := by
  let d := 37 * s - 1
  have hd' : d ≠ 0 := hd
  change (4 * s ^ 2 + ((114 * s - 6) / d) ^ 2 + 6 / d) -
    (4 / 3 : ℝ) * (3 * s ^ 2 + 7) = (656 * s ^ 2 - 1366 * s + 62) / (3 * d ^ 2)
  field_simp
  dsimp [d] at *
  ring

end CounterexampleCertificate
