module
public import Mathlib

public section
namespace GuthMaynard.Improvement

/-- Exact strip-to-window conversion, including a negative denominator. -/
theorem cubic_strip_window {m₁ m₂ m₃ v y h : ℝ} (hm₂ : m₂ ≠ 0) :
    |m₁*v+m₂*y+m₃| ≤ h ↔ |y-(-(m₁*v+m₃)/m₂)| ≤ h/|m₂| := by
  have hid : y-(-(m₁*v+m₃)/m₂) = (m₁*v+m₂*y+m₃)/m₂ := by field_simp; ring
  rw [hid,abs_div]
  exact (div_le_div_iff_of_pos_right (abs_pos.mpr hm₂)).symm

/-- Inversion interchanges the original slope and translation exactly. -/
theorem cubic_affine_inversion {m₁ m₂ m₃ v : ℝ} (hm₂ : m₂ ≠ 0) (hv : v ≠ 0) :
    (-(m₁*v+m₃)/m₂)/v = -(m₃*(1/v)+m₁)/m₂ := by
  field_simp
  ring

end GuthMaynard.Improvement
