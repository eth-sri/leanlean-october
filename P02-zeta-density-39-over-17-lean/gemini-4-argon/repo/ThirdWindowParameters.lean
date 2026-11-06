module
public import ThirdWindow

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Montgomery.RationalMoment

lemma affine_budget_of_endpoints {s P D x c₀ c₁ c₂ c₃ : ℝ}
    (hD : 0 < D) (hE : 0 < 2*s-1)
    (hx : P/D ≤ x) (hx' : x ≤ (D - 3*P*(1-s))/(D*(2*s-1)))
    (ha : 0 ≤ c₀*D + c₁*(3*P*(1-s)) + (c₂ + c₃*s)*P)
    (hα : 0 ≤ c₀*D*(2*s-1) + c₁*(3*P*(1-s))*(2*s-1) + (c₂ + c₃*s)*(D - 3*P*(1-s))) :
    0 ≤ c₀ + c₁*(3*P*(1-s)/D) + (c₂ + c₃*s)*x := by
  rw [show c₀ + c₁*(3*P*(1-s)/D) + (c₂ + c₃*s)*x = (c₂ + c₃*s)*x + (c₀ + c₁*(3*P*(1-s)/D)) by ring]
  apply affine_nonneg_between hx hx'
  · exact (div_nonneg ha hD.le).trans_eq (by field_simp [hD.ne']; ring)
  · exact (div_nonneg hα (mul_pos hD hE).le).trans_eq (by field_simp [hD.ne', hE.ne']; ring)

theorem third_window_of_endpoints (s P D : ℝ)
    (hs1 : 9/13 ≤ s) (hs2 : s ≤ 3/4) (hD : 0 < D)
    (hal : 69/100 * D ≤ P) (hah : P ≤ 4/5 * D)
    (hpl : 1/2 * D ≤ 3*P*(1-s)) (htII : (2-2*s+1/50)*D ≤ 3*P*(1-s))
    (ha0 : 0 ≤ 1*D + 0*(3*P*(1-s)) + (-1 + 0*s)*P)
    (hα0 : 0 ≤ 1*D*(2*s-1) + 0*(3*P*(1-s))*(2*s-1) + (-1 + 0*s)*(D - 3*P*(1-s)))
    (ha2 : 0 ≤ (-1)*D + (3/2)*(3*P*(1-s)) + (-4 + 6*s)*P)
    (hα2 : 0 ≤ (-1)*D*(2*s-1) + (3/2)*(3*P*(1-s))*(2*s-1) + (-4 + 6*s)*(D - 3*P*(1-s)))
    (ha3 : 0 ≤ 0*D + 1*(3*P*(1-s)) + (-2 + 2*s)*P)
    (hα3 : 0 ≤ 0*D*(2*s-1) + 1*(3*P*(1-s))*(2*s-1) + (-2 + 2*s)*(D - 3*P*(1-s)))
    (ha4 : 0 ≤ (-5/6)*D + 1*(3*P*(1-s)) + (-1 + 2*s)*P)
    (hα4 : 0 ≤ (-5/6)*D*(2*s-1) + 1*(3*P*(1-s))*(2*s-1) + (-1 + 2*s)*(D - 3*P*(1-s)))
    (ha5 : 0 ≤ (-2)*D + (5/2)*(3*P*(1-s)) + (-5 + 8*s)*P)
    (hα5 : 0 ≤ (-2)*D*(2*s-1) + (5/2)*(3*P*(1-s))*(2*s-1) + (-5 + 8*s)*(D - 3*P*(1-s)))
    (ha6 : 0 ≤ 0*D + 1*(3*P*(1-s)) + (-5 + 6*s)*P)
    (hα6 : 0 ≤ 0*D*(2*s-1) + 1*(3*P*(1-s))*(2*s-1) + (-5 + 6*s)*(D - 3*P*(1-s)))
    (ha7 : 0 ≤ (-5/6)*D + 1*(3*P*(1-s)) + (-4 + 6*s)*P)
    (hα7 : 0 ≤ (-5/6)*D*(2*s-1) + 1*(3*P*(1-s))*(2*s-1) + (-4 + 6*s)*(D - 3*P*(1-s)))
    (ha8 : 0 ≤ (-2)*D + (5/2)*(3*P*(1-s)) + (-8 + 12*s)*P)
    (hα8 : 0 ≤ (-2)*D*(2*s-1) + (5/2)*(3*P*(1-s))*(2*s-1) + (-8 + 12*s)*(D - 3*P*(1-s)))
    (ha9 : 0 ≤ (-1/8)*D + (49/40)*(3*P*(1-s)) + (-5 + 6*s)*P)
    (hα9 : 0 ≤ (-1/8)*D*(2*s-1) + (49/40)*(3*P*(1-s))*(2*s-1) + (-5 + 6*s)*(D - 3*P*(1-s)))
    (ha10 : 0 ≤ (-23/24)*D + (49/40)*(3*P*(1-s)) + (-4 + 6*s)*P)
    (hα10 : 0 ≤ (-23/24)*D*(2*s-1) + (49/40)*(3*P*(1-s))*(2*s-1) + (-4 + 6*s)*(D - 3*P*(1-s)))
    (ha11 : 0 ≤ (-17/8)*D + (109/40)*(3*P*(1-s)) + (-8 + 12*s)*P)
    (hα11 : 0 ≤ (-17/8)*D*(2*s-1) + (109/40)*(3*P*(1-s))*(2*s-1) + (-8 + 12*s)*(D - 3*P*(1-s)))
    (ha12 : 0 ≤ (-2)*D + 4*(3*P*(1-s)) + (-12 + 16*s)*P)
    (hα12 : 0 ≤ (-2)*D*(2*s-1) + 4*(3*P*(1-s))*(2*s-1) + (-12 + 16*s)*(D - 3*P*(1-s)))
    (ha13 : 0 ≤ (-2)*D + 2*(3*P*(1-s)) + (-9 + 14*s)*P)
    (hα13 : 0 ≤ (-2)*D*(2*s-1) + 2*(3*P*(1-s))*(2*s-1) + (-9 + 14*s)*(D - 3*P*(1-s)))
    (ha14 : 0 ≤ (-3)*D + (5/2)*(3*P*(1-s)) + (-8 + 14*s)*P)
    (hα14 : 0 ≤ (-3)*D*(2*s-1) + (5/2)*(3*P*(1-s))*(2*s-1) + (-8 + 14*s)*(D - 3*P*(1-s)))
    (ha15 : 0 ≤ (-9/4)*D + (29/12)*(3*P*(1-s)) + (-9 + 14*s)*P)
    (hα15 : 0 ≤ (-9/4)*D*(2*s-1) + (29/12)*(3*P*(1-s))*(2*s-1) + (-9 + 14*s)*(D - 3*P*(1-s)))
    (ha16 : 0 ≤ (-1)*D + (5/4)*(3*P*(1-s)) + (-4 + 6*s)*P)
    (hα16 : 0 ≤ (-1)*D*(2*s-1) + (5/4)*(3*P*(1-s))*(2*s-1) + (-4 + 6*s)*(D - 3*P*(1-s))) :
    ThirdWindow s (P/D) (3*P*(1-s)/D) ((D - 3*P*(1-s))/(D*(2*s-1))) := by
  have hE : 0 < 2*s-1 := by linarith
  have hEn : -1 + s * 2 ≠ 0 := by linarith
  refine ⟨hs1, hs2, (le_div_iff₀ hD).mpr hal, (div_le_iff₀ hD).mpr hah,
    (le_div_iff₀ hD).mpr hpl, by ring,
    by field_simp [hD.ne', hE.ne', hEn]; ring_nf; field_simp [hD.ne', hEn]; ring,
    (le_div_iff₀ hD).mpr htII, ?_⟩
  intro x hx hx'
  have h0 := affine_budget_of_endpoints hD hE hx hx' ha0 hα0
  have h2 := affine_budget_of_endpoints hD hE hx hx' ha2 hα2
  have h3 := affine_budget_of_endpoints hD hE hx hx' ha3 hα3
  have h4 := affine_budget_of_endpoints hD hE hx hx' ha4 hα4
  have h5 := affine_budget_of_endpoints hD hE hx hx' ha5 hα5
  have h6 := affine_budget_of_endpoints hD hE hx hx' ha6 hα6
  have h7 := affine_budget_of_endpoints hD hE hx hx' ha7 hα7
  have h8 := affine_budget_of_endpoints hD hE hx hx' ha8 hα8
  have h9 := affine_budget_of_endpoints hD hE hx hx' ha9 hα9
  have h10 := affine_budget_of_endpoints hD hE hx hx' ha10 hα10
  have h11 := affine_budget_of_endpoints hD hE hx hx' ha11 hα11
  have h12 := affine_budget_of_endpoints hD hE hx hx' ha12 hα12
  have h13 := affine_budget_of_endpoints hD hE hx hx' ha13 hα13
  have h14 := affine_budget_of_endpoints hD hE hx hx' ha14 hα14
  have h15 := affine_budget_of_endpoints hD hE hx hx' ha15 hα15
  have h16 := affine_budget_of_endpoints hD hE hx hx' ha16 hα16
  dsimp only [thirdAmplifierExponent]
  refine ⟨max_le (by linarith) (max_le (by norm_num) (by linarith)),
    max_le (by linarith) (max_le (by linarith) (by linarith)),
    max_le (by linarith) (max_le (by linarith) (by linarith)),
    max_le (by linarith) (max_le (by linarith) (by linarith)),
    by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem third_window_first (s : ℝ) (hl : (12/17:ℝ) ≤ s) (hr : s ≤ (5/7:ℝ)) :
    ThirdWindow s (2/(8*s-3)) (3*2*(1-s)/(8*s-3)) ((8*s-3 - 3*2*(1-s))/((8*s-3)*(2*s-1))) := by
  have h₁ := mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr hr)
  apply third_window_of_endpoints <;> nlinarith [sq_nonneg (5/7 - s), h₁, sq_nonneg (s - 12/17)]

theorem third_window_second (s : ℝ) (hl : (5/7:ℝ) ≤ s) (hr : s ≤ (113/153:ℝ)) :
    ThirdWindow s (4/(9*s-1)) (3*4*(1-s)/(9*s-1)) ((9*s-1 - 3*4*(1-s))/((9*s-1)*(2*s-1))) := by
  have h₁ := mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr hr)
  apply third_window_of_endpoints <;> nlinarith [sq_nonneg (113/153 - s), h₁, sq_nonneg (s - 5/7)]

theorem third_window_parameters (s : ℝ) (hl : (113/153:ℝ) ≤ s) (hr : s ≤ (3/4:ℝ)) :
    ThirdWindow s (85/(153*s+7)) (3*85*(1-s)/(153*s+7)) ((153*s+7 - 3*85*(1-s))/((153*s+7)*(2*s-1))) := by
  have h₁ := mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr hr)
  apply third_window_of_endpoints <;> nlinarith [sq_nonneg (3/4 - s), h₁, sq_nonneg (s - 113/153)]

