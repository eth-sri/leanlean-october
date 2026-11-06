module
public import DensityWindowBudgets

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Montgomery.RationalMoment

local notation "D" s => (8 * s - 3)
local notation "E" s => (2 * s - 1)
local notation "L" s => ((5/7 : ℝ) - s)
local notation "R" s => (s - (12/17 : ℝ))
local notation "A" s => ((14 * s - 9) / ((D s) * (E s)))
local notation "B" s => (2 / D s)
local notation "P" s => (6 * (1 - s) / D s)

/-- All endpoints and length-window budgets for the first two-term branch. -/
theorem two_term_window_first (s : ℝ) (hl : (12/17:ℝ) ≤ s) (hr : s ≤ (5/7:ℝ)) :
    TwoTermWindow s (B s) (P s) (A s) := by
  have hD : 0 < 8*s-3 := by linarith
  have hE : 0 < 2*s-1 := by linarith
  have hDn : -3+s*8 ≠ 0 := by linarith
  have hEn : -1+s*2 ≠ 0 := by linarith
  have hPn : ((3:ℝ) + (-14:ℝ)*s + (16:ℝ)*s^2) ≠ 0 := by nlinarith only [mul_pos hD hE]
  ring_nf at hDn hEn hPn
  refine {
    sigma_low := by linarith
    sigma_high := by linarith
    p_identity := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf
    mean_identity := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
    a_low := by
      have hid : (B s)-(7/10:ℝ) = ((41/10:ℝ) + (-28/5:ℝ)*s)/((D s)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf
      have hpoly : 0 ≤ (41/10:ℝ) + (-28/5:ℝ)*s := by
        have h₀ : 0 ≤ (4165/2:ℝ)*(L s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (17493/5:ℝ)*((R s)*(L s)) :=
          mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (14161/10:ℝ)*(R s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (B s)-(7/10:ℝ) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    a_high := by
      have hid : (4/5:ℝ)-(B s) = ((-22/5:ℝ) + (32/5:ℝ)*s)/((D s)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf
      have hpoly : 0 ≤ (-22/5:ℝ) + (32/5:ℝ)*s := by
        have h₀ : 0 ≤ (1666:ℝ)*(L s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (20468/5:ℝ)*((R s)*(L s)) :=
          mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (12138/5:ℝ)*(R s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (4/5:ℝ)-(B s) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    p_low := by
      have hid : (P s)-(3/5:ℝ) = ((39/5:ℝ) + (-54/5:ℝ)*s)/((D s)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (39/5:ℝ) + (-54/5:ℝ)*s := by
        have h₀ : 0 ≤ (2499:ℝ)*(L s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (18564/5:ℝ)*((R s)*(L s)) :=
          mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (6069/5:ℝ)*(R s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (P s)-(3/5:ℝ) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    alpha_low := by
      have hid : (A s)-(B s) = ((-7:ℝ) + (10:ℝ)*s)/((D s)*(E s)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (-7:ℝ) + (10:ℝ)*s := by
        have h₀ : 0 ≤ (833:ℝ)*(L s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (2856:ℝ)*((R s)*(L s)) :=
          mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (2023:ℝ)*(R s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (A s)-(B s) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    alpha_high := by
      have hid : 1-(A s) = ((12:ℝ) + (-28:ℝ)*s + (16:ℝ)*s^2)/((D s)*(E s)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (12:ℝ) + (-28:ℝ)*s + (16:ℝ)*s^2 := by
        have h₀ : 0 ≤ (2940:ℝ)*(L s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (5236:ℝ)*((R s)*(L s)) :=
          mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (2312:ℝ)*(R s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ 1-(A s) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    energy_range := by
      have hid : (P s)-2*(1-(B s)) = ((16:ℝ) + (-22:ℝ)*s)/((D s)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (16:ℝ) + (-22:ℝ)*s := by
        have h₀ : 0 ≤ (6664:ℝ)*(L s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (10710:ℝ)*((R s)*(L s)) :=
          mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (4046:ℝ)*(R s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (P s)-2*(1-(B s)) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    amplifier_lower := by
      have hid : (P s)+(A s)*(6*s-5) = ((39:ℝ) + (-106:ℝ)*s + (72:ℝ)*s^2)/((D s)*(E s)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (39:ℝ) + (-106:ℝ)*s + (72:ℝ)*s^2 := by
        have h₀ : 0 ≤ (735:ℝ)*(L s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (952:ℝ)*((R s)*(L s)) :=
          mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (289:ℝ)*(R s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (P s)+(A s)*(6*s-5) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    cubic_lower := by
      have hid : (P s)+(B s)*(6*s-4)-(4/5:ℝ) = ((2/5:ℝ) + (-2/5:ℝ)*s)/((D s)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (2/5:ℝ) + (-2/5:ℝ)*s := by
        have h₀ : 0 ≤ (1666:ℝ)*(L s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (16422/5:ℝ)*((R s)*(L s)) :=
          mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (8092/5:ℝ)*(R s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (P s)+(B s)*(6*s-4)-(4/5:ℝ) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    amplifier_upper := by
      have hid : 1-((P s)+(A s)*(6*s-4)) = ((-27:ℝ) + (78:ℝ)*s + (-56:ℝ)*s^2)/((D s)*(E s)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (-27:ℝ) + (78:ℝ)*s + (-56:ℝ)*s^2 := by
        have h₀ : 0 ≤ (2205:ℝ)*(L s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (4284:ℝ)*((R s)*(L s)) :=
          mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (2023:ℝ)*(R s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ 1-((P s)+(A s)*(6*s-4)) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    cubic_balance := by
      have hid : 5*(P s)/2+(B s)*(12*s-8)-2 = ((5:ℝ) + (-7:ℝ)*s)/((D s)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (5:ℝ) + (-7:ℝ)*s := by
        have h₀ : 0 ≤ (833:ℝ)*(L s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (833:ℝ)*((R s)*(L s)) :=
          mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (0:ℝ)*(R s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ 5*(P s)/2+(B s)*(12*s-8)-2 := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    energy_first := by
      have hid : 2*(P s)-(1+(A s)*(6-8*s)) = ((39:ℝ) + (-106:ℝ)*s + (72:ℝ)*s^2)/((D s)*(E s)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (39:ℝ) + (-106:ℝ)*s + (72:ℝ)*s^2 := by
        have h₀ : 0 ≤ (735:ℝ)*(L s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (952:ℝ)*((R s)*(L s)) :=
          mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (289:ℝ)*(R s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ 2*(P s)-(1+(A s)*(6-8*s)) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    energy_resonant := by
      have hid : (P s)-(1+(B s)*(9/2-7*s)) = ((0:ℝ))/((D s)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (0:ℝ) := by
        norm_num
      have hh : 0 ≤ (P s)-(1+(B s)*(9/2-7*s)) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
    typeII := by
      have hid : (P s)-(2-2*s+1/25) = ((303/25:ℝ) + (-708/25:ℝ)*s + (16:ℝ)*s^2)/((D s)) := by field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring_nf; field_simp [hD.ne',hE.ne',hDn,hEn,hPn]; ring
      have hpoly : 0 ≤ (303/25:ℝ) + (-708/25:ℝ)*s + (16:ℝ)*s^2 := by
        have h₀ : 0 ≤ (7203/5:ℝ)*(L s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        have h₁ : 0 ≤ (54978/25:ℝ)*((R s)*(L s)) :=
          mul_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
        have h₂ : 0 ≤ (19363/25:ℝ)*(R s)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
        nlinarith only [h₀,h₁,h₂]
      have hh : 0 ≤ (P s)-(2-2*s+1/25) := by rw [hid]; exact div_nonneg hpoly (by positivity)
      linarith only [hh]
  }

end Montgomery.RationalMoment
