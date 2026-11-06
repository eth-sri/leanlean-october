module
public import ActualLongTailReduction
public import RetunedDetectorParameters

@[expose] public section
set_option autoImplicit false
noncomputable section
open Filter MathCollab.Density.Stronger MathCollab.Density
namespace Montgomery.RationalMoment.RightDetector

theorem criticalMeanThreshold_dominates_power {C σ a δ q K : ℝ}
    (hC : 0 < C) (_hK : 0 < K)
    (hmargin : q+δ/2 < (3*a/4)*(σ-1/2)) :
    ∀ᶠ T : ℝ in atTop, K*T^q ≤ criticalMeanThreshold C σ a δ T := by
  let e : ℝ := ((3*a/4)*(σ-1/2)-q-δ/2)/3
  have he : 0 < e := by dsimp [e]; linarith
  have hconst := (tendsto_rpow_atTop he).eventually
    (eventually_ge_atTop (48*C*K))
  filter_upwards [hconst,log_pow_eventually_le_rpow 1 he,
    eventually_ge_atTop (2:ℝ)] with T hc hlog hT
  have hTp : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hsqrt : Real.sqrt (detectorX δ T)=T^(δ/2) := by
    rw [Real.sqrt_eq_rpow,detectorX,← Real.rpow_mul hTp.le]
    congr 1
    ring
  have hYpow : (detectorY a T)^((σ-1/2)/2)=T^((3*a/4)*(σ-1/2)) := by
    rw [detectorY,smoothingExponent,← Real.rpow_mul hTp.le]
    congr 1
    ring
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  unfold criticalMeanThreshold
  apply (le_div_iff₀ (by have := Real.log_pos (by linarith : 1<T); unfold detectorX; positivity)).mpr
  rw [hsqrt,hYpow]
  calc
    _ = (48*C*K)*T^q*T^(δ/2)*Real.log T := by ring
    _ ≤ T^e*T^q*T^(δ/2)*T^e := by gcongr; simpa only [pow_one] using hlog
    _ = T^(q+δ/2+2*e) := by
      rw [← Real.rpow_add hTp,← Real.rpow_add hTp,← Real.rpow_add hTp]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hT1 (by dsimp [e]; linarith)

