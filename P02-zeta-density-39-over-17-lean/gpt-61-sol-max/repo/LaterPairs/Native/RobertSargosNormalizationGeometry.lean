module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.RobertSargosNormalizationCoordinates

@[expose] public section
set_option maxHeartbeats 0


                                                                                         


namespace TaoTrudgianYang2025

section
variable (r q₁ q₂ h₁ h₂ d j k : ℝ)
    (hj : j ≠ 0) (hk : k ≠ 0)
include r q₁ q₂ h₁ h₂ d j k hj hk

theorem robertSargos_linear_div  :
    (r/j)*(d/k)+(h₁/j)*(q₁/k)-(h₂/j)*(q₂/k) =
      (r*d+h₁*q₁-h₂*q₂)/(j*k) := by
  field_simp

theorem robertSargos_reduced_div  :
    robertSargosReduced (r/j) (q₁/k) (q₂/k) (h₁/j) (h₂/j) (d/k) =
      robertSargosReduced r q₁ q₂ h₁ h₂ d/(j*k^2) := by
  unfold robertSargosReduced
  field_simp
end


section
variable {a : ℤ} {g : ℕ} {A B : ℝ}
    (hg : 0 < g) (hdiv : (g:ℤ) ∣ a)
include a g A B hg hdiv

theorem integer_ediv_interval_support 
    (hab : (a:ℝ) ∈ Set.Icc A B) :
    ((a/(g:ℤ):ℤ):ℝ) ∈ Set.Icc (A/(g:ℝ)) (B/(g:ℝ)) := by
  have hgR : (0:ℝ) < g := by exact_mod_cast hg
  rw [Int.cast_div_charZero hdiv,Int.cast_natCast]
  exact ⟨div_le_div_of_nonneg_right hab.1 hgR.le,
    div_le_div_of_nonneg_right hab.2 hgR.le⟩

theorem integer_ediv_abs_support 
    (hab : |(a:ℝ)| ∈ Set.Icc A B) :
    |((a/(g:ℤ):ℤ):ℝ)| ∈ Set.Icc (A/(g:ℝ)) (B/(g:ℝ)) := by
  have hgR : (0:ℝ) < g := by exact_mod_cast hg
  rw [Int.cast_div_charZero hdiv,Int.cast_natCast,abs_div,abs_of_pos hgR]
  exact ⟨div_le_div_of_nonneg_right hab.1 hgR.le,
    div_le_div_of_nonneg_right hab.2 hgR.le⟩
end



