module
public import ThirdWindow

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Montgomery.RationalMoment

theorem third_window_parameters (s : ℝ) (hl : (113/153:ℝ) ≤ s) (hr : s ≤ (3/4:ℝ)) :
    ThirdWindow s (85/(153*s+7)) (255*(1-s)/(153*s+7)) ((408*s-248)/((153*s+7)*(2*s-1))) := by
  set a := 85/(153*s+7)
  set p := 255*(1-s)/(153*s+7)
  set α := (408*s-248)/((153*s+7)*(2*s-1))
  have hD : 0 < 153*s+7 := by linarith
  have hE : 0 < 2*s-1 := by linarith
  have hDE : 0 < (153*s+7)*(2*s-1) := mul_pos hD hE
  have ha0 : 0 ≤ a := by positivity
  have ha : a*(153*s+7) = 85 := div_mul_cancel₀ _ hD.ne'
  have hp : p*(153*s+7) = 255*(1-s) := div_mul_cancel₀ _ hD.ne'
  have hα : α*((153*s+7)*(2*s-1)) = 408*s-248 := div_mul_cancel₀ _ hDE.ne'
  clear_value a p α
  have hsa : s*(a*(153*s+7)) = 85*s := by rw [ha]; ring
  have hsp : s*(p*(153*s+7)) = s*(255*(1-s)) := by rw [hp]
  have hsα : s*(α*((153*s+7)*(2*s-1))) = s*(408*s-248) := by rw [hα]
  have hq : 0 ≤ (s - 113/153)*(3/4 - s) := mul_nonneg (by linarith) (by linarith)
  have hqs : 0 ≤ (2*s-1)*((s - 113/153)*(3/4 - s)) := mul_nonneg hE.le hq
  refine {
    sigma_low := by linarith
    sigma_high := by linarith
    a_low := by nlinarith only [hl, hr, hD, ha, hq]
    a_high := by nlinarith only [hl, hr, hD, ha, hq]
    p_low := by nlinarith only [hl, hr, hD, hp, hq]
    alpha_low := by nlinarith only [hl, hr, hD, hE, hDE, ha, hα, hsa, hq]
    alpha_high := by nlinarith only [hl, hr, hD, hE, hDE, hα, hq]
    p_identity := by nlinarith only [hD, ha, hp, hsa]
    mean_identity := by nlinarith only [hD, hE, hDE, hp, hα, hsp, hsα]
    typeII := by nlinarith only [hl, hr, hD, hp, hq]
    budgets := ?_
  }
  intro x hx hx'
  have hxa : 85 ≤ x*(153*s+7) := by have := mul_le_mul_of_nonneg_right hx hD.le; linarith
  have hsxa : 85*s ≤ s*(x*(153*s+7)) := by have := mul_le_mul_of_nonneg_left hxa (show 0 ≤ s by linarith); linarith
  have hxα : x*((153*s+7)*(2*s-1)) ≤ 408*s-248 := by have := mul_le_mul_of_nonneg_right hx' hDE.le; linarith
  have hsxα : s*(x*((153*s+7)*(2*s-1))) ≤ s*(408*s-248) := by have := mul_le_mul_of_nonneg_left hxα (show 0 ≤ s by linarith); linarith
  dsimp only; unfold thirdAmplifierExponent
  refine ⟨max_le (by nlinarith only [hl, hr, hD, hE, hDE, hxα, hq])
      (max_le (by norm_num) (by nlinarith only [hl, hr, hD, hE, hDE, hp, hsp, hxa, hsxa, hxα, hsxα, hq, hqs])),
    max_le (by nlinarith only [hl, hr, hD, hE, hDE, hp, hsp, hxa, hsxa, hxα, hsxα, hq, hqs])
      (max_le (by nlinarith only [hl, hr, hD, hE, hDE, hp, hsp, hxa, hsxa, hxα, hsxα, hq, hqs])
        (by nlinarith only [hl, hr, hD, hE, hDE, hp, hsp, hxa, hsxa, hxα, hsxα, hq, hqs])),
    max_le (by nlinarith only [hl, hr, hD, hE, hDE, hp, hsp, hxa, hsxa, hxα, hsxα, hq, hqs])
      (max_le (by nlinarith only [hl, hr, hD, hE, hDE, hp, hsp, hxa, hsxa, hxα, hsxα, hq, hqs])
        (by nlinarith only [hl, hr, hD, hE, hDE, hp, hsp, hxa, hsxa, hxα, hsxα, hq, hqs])),
    max_le (by nlinarith only [hl, hr, hD, hE, hDE, hp, hsp, hxa, hsxa, hxα, hsxα, hq, hqs])
      (max_le (by nlinarith only [hl, hr, hD, hE, hDE, hp, hsp, hxa, hsxa, hxα, hsxα, hq, hqs])
        (by nlinarith only [hl, hr, hD, hE, hDE, hp, hsp, hxa, hsxa, hxα, hsxα, hq, hqs])),
    by nlinarith only [hl, hr, hD, hE, hDE, hp, hsp, hxa, hsxa, hxα, hsxα, hq, hqs],
    by nlinarith only [hl, hr, hD, hE, hDE, hp, hsp, hxa, hsxa, hxα, hsxα, hq, hqs],
    by nlinarith only [hl, hr, hD, hE, hDE, hp, hsp, hxa, hsxa, hxα, hsxα, hq, hqs],
    by nlinarith only [hl, hr, hD, hE, hDE, hp, hsp, hxa, hsxa, hxα, hsxα, hq, hqs],
    by nlinarith only [hl, hr, hD, hE, hDE, hp, hsp, hxa, hsxa, hxα, hsxα, hq, hqs]⟩

end Montgomery.RationalMoment
