module
public import DensityWindowBudgets

@[expose] public section
set_option autoImplicit false
namespace Montgomery.RationalMoment

theorem two_term_window_first (s : ℝ) (hl : (12/17:ℝ) ≤ s) (hr : s ≤ (5/7:ℝ)) :
    TwoTermWindow s (2/(8*s-3)) (6*(1-s)/(8*s-3)) ((14*s-9)/((8*s-3)*(2*s-1))) := by
  set a := 2/(8*s-3)
  set p := 6*(1-s)/(8*s-3)
  set α := (14*s-9)/((8*s-3)*(2*s-1))
  have hD : 0 < 8*s-3 := by linarith
  have hE : 0 < 2*s-1 := by linarith
  have hDE : 0 < (8*s-3)*(2*s-1) := mul_pos hD hE
  have ha : a*(8*s-3) = 2 := div_mul_cancel₀ _ hD.ne'
  have hp : p*(8*s-3) = 6*(1-s) := div_mul_cancel₀ _ hD.ne'
  have hα : α*((8*s-3)*(2*s-1)) = 14*s-9 := div_mul_cancel₀ _ hDE.ne'
  have hsα : s*(α*((8*s-3)*(2*s-1))) = s*(14*s-9) := by rw [hα]
  have hq : 0 ≤ (s - 12/17)*(5/7 - s) := mul_nonneg (by linarith) (by linarith)
  exact {
    sigma_low := by linarith
    sigma_high := by linarith
    a_low := by nlinarith
    a_high := by nlinarith
    p_low := by nlinarith
    alpha_low := by nlinarith
    alpha_high := by nlinarith
    p_identity := by nlinarith
    mean_identity := by nlinarith
    energy_range := by nlinarith
    amplifier_lower := by nlinarith
    cubic_lower := by nlinarith
    amplifier_upper := by nlinarith
    cubic_balance := by nlinarith
    energy_first := by nlinarith
    energy_resonant := by nlinarith
    typeII := by nlinarith
  }

end Montgomery.RationalMoment
