module
import Mathlib
public import AdjacentWindow

@[expose] public section

set_option maxHeartbeats 1200000
namespace Montgomery.RationalMoment

/-- All endpoints and length-window budgets for the second two-term branch. -/
theorem adjacent_window_second (s : ℝ) (hl : (5/7:ℝ) ≤ s) (hr : s ≤ (113/153:ℝ)) :
    AdjacentWindow s (4/(9*s-1)) (12*(1-s)/(9*s-1)) ((21*s-13)/((9*s-1)*(2*s-1))) := by
  have hD : 0 < 9*s-1 := by linarith
  have hE : 0 < 2*s-1 := by linarith
  have hDn : -1+s*9 ≠ 0 := by linarith
  have hEn : -1+s*2 ≠ 0 := by linarith
  have hPn : ((1:ℝ) + (-11:ℝ)*s + (18:ℝ)*s^2) ≠ 0 := by nlinarith only [mul_pos hD hE]
  ring_nf at hDn hEn hPn
  refine {
    sigma_low := by linarith
    sigma_high := by linarith
    p_identity := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf
    mean_identity := by grind
    a_low := by field_simp <;> nlinarith
    a_high := by field_simp <;> nlinarith
    p_low := by field_simp <;> nlinarith
    alpha_low := by
      have hid : ((21*s-13)/((9*s-1)*(2*s-1)))-(4/(9*s-1)) = ((-9:ℝ) + (13:ℝ)*s)/((9*s-1)*(2*s-1)) := by grind
      have hpoly : 0 ≤ (-9:ℝ) + (13:ℝ)*s := by linarith
      have hh : 0 ≤ ((21*s-13)/((9*s-1)*(2*s-1)))-(4/(9*s-1)) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    alpha_high := by
      have hid : 1-((21*s-13)/((9*s-1)*(2*s-1))) = ((14:ℝ) + (-32:ℝ)*s + (18:ℝ)*s^2)/((9*s-1)*(2*s-1)) := by grind
      have hpoly : 0 ≤ (14:ℝ) + (-32:ℝ)*s + (18:ℝ)*s^2 := by nlinarith
      have hh : 0 ≤ 1-((21*s-13)/((9*s-1)*(2*s-1))) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    amplifier_lower := by
      have hid : (12*(1-s)/(9*s-1))+((21*s-13)/((9*s-1)*(2*s-1)))*(6*s-5) = ((53:ℝ) + (-147:ℝ)*s + (102:ℝ)*s^2)/((9*s-1)*(2*s-1)) := by grind
      have hpoly : 0 ≤ (53:ℝ) + (-147:ℝ)*s + (102:ℝ)*s^2 := by nlinarith
      have hh : 0 ≤ (12*(1-s)/(9*s-1))+((21*s-13)/((9*s-1)*(2*s-1)))*(6*s-5) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    cubic_lower := by
      have hid : (12*(1-s)/(9*s-1))+(4/(9*s-1))*(6*s-4)-(4/5:ℝ) = ((-16/5:ℝ) + (24/5:ℝ)*s)/((9*s-1)) := by grind
      have hpoly : 0 ≤ (-16/5:ℝ) + (24/5:ℝ)*s := by linarith
      have hh : 0 ≤ (12*(1-s)/(9*s-1))+(4/(9*s-1))*(6*s-4)-(4/5:ℝ) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    amplifier_upper := by
      have hid : 1-((12*(1-s)/(9*s-1))+((21*s-13)/((9*s-1)*(2*s-1)))*(6*s-4)) = ((-39:ℝ) + (115:ℝ)*s + (-84:ℝ)*s^2)/((9*s-1)*(2*s-1)) := by grind
      have hpoly : 0 ≤ (-39:ℝ) + (115:ℝ)*s + (-84:ℝ)*s^2 := by nlinarith
      have hh : 0 ≤ 1-((12*(1-s)/(9*s-1))+((21*s-13)/((9*s-1)*(2*s-1)))*(6*s-4)) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    cubic_balance := by grind
    energy_first := by
      have hid : 2*(12*(1-s)/(9*s-1))-(1+((21*s-13)/((9*s-1)*(2*s-1)))*(6-8*s)) = ((53:ℝ) + (-147:ℝ)*s + (102:ℝ)*s^2)/((9*s-1)*(2*s-1)) := by grind
      have hpoly : 0 ≤ (53:ℝ) + (-147:ℝ)*s + (102:ℝ)*s^2 := by nlinarith
      have hh : 0 ≤ 2*(12*(1-s)/(9*s-1))-(1+((21*s-13)/((9*s-1)*(2*s-1)))*(6-8*s)) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    energy_resonant := by field_simp <;> nlinarith
    energy_adjacent_third := by
      have hid : (5/2)*(12*(1-s)/(9*s-1))+(4/(9*s-1))*(14*s-8)-3 = ((1:ℝ) + (-1:ℝ)*s)/((9*s-1)) := by grind
      have hpoly : 0 ≤ (1:ℝ) + (-1:ℝ)*s := by linarith
      have hh : 0 ≤ (5/2)*(12*(1-s)/(9*s-1))+(4/(9*s-1))*(14*s-8)-3 := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    energy_adjacent_fourth := by field_simp <;> nlinarith
    typeII := by
      have hid : (12*(1-s)/(9*s-1))-(2-2*s+1/50) = ((701/50:ℝ) + (-1609/50:ℝ)*s + (18:ℝ)*s^2)/((9*s-1)) := by grind
      have hpoly : 0 ≤ (701/50:ℝ) + (-1609/50:ℝ)*s + (18:ℝ)*s^2 := by nlinarith
      have hh : 0 ≤ (12*(1-s)/(9*s-1))-(2-2*s+1/50) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
  }


