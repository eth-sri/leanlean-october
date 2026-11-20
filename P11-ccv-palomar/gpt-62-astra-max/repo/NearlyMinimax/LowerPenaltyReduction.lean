module

public import NearlyMinimax.LowerRawCostReduction


@[expose] public section

/-! The genuine mass-exception penalty is negligible compared with the
squared lower saddle scale. Constants are fixed before any model domain. -/
noncomputable section
open Filter
open scoped Topology
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- The exact numeric lower envelope, after the true tilted exceptional
penalty, dominates a fixed positive multiple of the manuscript's squared
scale. No statistical risk or desired-rate premise is used. -/
theorem eventually_actual_lowerSaddle_penalized_rate_square
    {s d a b cf CG ctr cm Cmgf DV : ℝ}
    (hs : 1 < s) (hd : 4*s < d) (ha : 0 < a) (hab : a < b)
    (hcf : 0 < cf) (hCG : 0 < CG) (hctr : 0 < ctr)
    (hcm : 0 < cm) (hCmgf : 0 < Cmgf) (C : ℝ) :
    let coefficient := lowerSaddleCoefficient s d (densityIntervalExponent a b)
    let theta := lowerSaddleTheta s d (densityIntervalExponent a b)
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x in atTop,
      let m := coefficient
      let θ := theta
      let τM := shrunkDensityExponent a b
      (c*rateScale (rateExponent s d) (stretchConstant s d (densityIntervalExponent a b))
        (lowerLogPower s d) x)^2 ≤
      ctr/(3*CG)*(lowerSaddleRisk s d m θ C cf τM x)^2-
        DV^2*lowerSaddleExceptionalTail d m θ C (cm^2/(8*Cmgf)) x := by
  intro coefficient
  intro theta
  obtain ⟨c₀,A,hc₀,hA,hbracket⟩ := actual_lowerSaddleRisk_rate_bracket hs hd ha hab hcf C
  let α := ctr/(3*CG)
  have hα : 0 < α := by positivity
  let q := α*c₀^2/2
  have hq : 0 < q := by positivity
  let c := Real.sqrt q
  have hcsq  := Real.sq_sqrt hq.le
  let ratio := q/(DV^2+1)
  have htol : 0 < ratio := by positivity
  refine ⟨c,(Real.sqrt_pos.mpr hq),?_⟩
  filter_upwards [hbracket,((actual_lowerSaddle_exceptionalTail_over_Psi_tends_zero hs hd ha hab hcm hCmgf C).eventually (eventually_lt_nhds htol))] with x hb hx
  let S := rateScale (rateExponent s d) (stretchConstant s d (densityIntervalExponent a b))
    (lowerLogPower s d) x
  let R := lowerSaddleRisk s d (coefficient)
    (theta) C cf (shrunkDensityExponent a b) x
  let ε := lowerSaddleExceptionalTail d (coefficient)
    (theta) C (cm^2/(8*Cmgf)) x
  have hS : 0 < S := rateScale_pos ..
  have hsq  := (sq_le_sq₀ (by positivity) (lowerSaddleRisk_positive hcf _).le).mpr (hb.1)
  have hε : ε ≤ (ratio)*S^2 := by
    exact (div_le_iff₀ (by positivity)).mp hx.le
  have hfrac : DV^2*(ratio) ≤ q := by
    have hp  := hq.le
    have he : DV^2*(ratio) = (DV^2*q)/(DV^2+1) := by ring
    rw [he]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith only [hp]
  have hp1 := mul_le_mul_of_nonneg_left hε (sq_nonneg DV)
  have hp2 := mul_le_mul_of_nonneg_right hfrac (sq_nonneg S)
  have hmain := mul_le_mul_of_nonneg_left hsq hα.le
  rw [mul_pow,hcsq]
  grind

end NearlyMinimax
