module
public import AdjacentWindow

@[expose] public section
set_option autoImplicit false
namespace Montgomery.RationalMoment

theorem adjacent_window_second (s : ℝ) (hl : (5/7:ℝ) ≤ s) (hr : s ≤ (113/153:ℝ)) :
    AdjacentWindow s (4/(9*s-1)) (12*(1-s)/(9*s-1)) ((21*s-13)/((9*s-1)*(2*s-1))) := by
  set a := 4/(9*s-1)
  set p := 12*(1-s)/(9*s-1)
  set α := (21*s-13)/((9*s-1)*(2*s-1))
  have hD : 0 < 9*s-1 := by linarith
  have hE : 0 < 2*s-1 := by linarith
  have hDE : 0 < (9*s-1)*(2*s-1) := mul_pos hD hE
  have ha : a*(9*s-1) = 4 := div_mul_cancel₀ _ hD.ne'
  have hp : p*(9*s-1) = 12*(1-s) := div_mul_cancel₀ _ hD.ne'
  have hα : α*((9*s-1)*(2*s-1)) = 21*s-13 := div_mul_cancel₀ _ hDE.ne'
  have hsα : s*(α*((9*s-1)*(2*s-1))) = s*(21*s-13) := by rw [hα]
  have hq : 0 ≤ (s - 5/7)*(113/153 - s) := mul_nonneg (by linarith) (by linarith)
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
    amplifier_lower := by nlinarith
    cubic_lower := by nlinarith
    amplifier_upper := by nlinarith
    cubic_balance := by nlinarith
    energy_first := by nlinarith
    energy_resonant := by nlinarith
    energy_adjacent_third := by nlinarith
    energy_adjacent_fourth := by nlinarith
    typeII := by nlinarith
  }

end Montgomery.RationalMoment
