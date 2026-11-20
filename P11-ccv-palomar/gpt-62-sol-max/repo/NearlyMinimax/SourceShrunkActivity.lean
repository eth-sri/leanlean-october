module

public import NearlyMinimax.SourceTotalActivity
public import NearlyMinimax.SourcePairActivityConversion


@[expose] public section

/-! The complete source activity bound at the actual common cutoff and
actual shrunk density interval. Its constant is fixed before M and N. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem sourceRows_shrunk_activity_bound {d k D M q : ℕ} [NeZero d] (hd : 0 < d) (hD : 1 ≤ D)
    (a b C lam N μ c0 q1 q2 : ℝ) (ha : 0 < a)
    (hshrink : a+(M : ℝ)⁻¹ < b-(M : ℝ)⁻¹) (htau : shrunkDensityExponent a b M ≤ c0)
    (hc0 : 1 ≤ c0) (hN : 1 ≤ N) (hμ : 0 ≤ μ) (hbase1 : μ*(1+Real.log N) ≤ 1)
    (hDN : (D : ℝ)*Real.exp (c0*(D : ℝ)) ≤ N)
    (hq1 : q1 = higherBandGeometricRatio d D (higherBandSourceCact d a b c0 lam)
      (1+Real.log N) (μ*(1+Real.log N)) 1)
    (hq2 : q2 = higherBandGeometricRatio d D (higherBandSourceCact d a b c0 lam)
      (1+Real.log N) (μ*(1+Real.log N)) 2)
    (hq1h : q1 ≤ 1/2) (hq21 : q2 ≤ q1) (hsmall : (D : ℝ)^2*q1 ≤ 1) :
    highRowTotalMass (sourceRowData d k D M q (a+1/(M : ℝ)) (b-1/(M : ℝ)) C lam
      (N*Real.exp (-c0*(D : ℝ))) N μ).rowMass ≤
      sourceActivityConstant d q C (uniformOrdinaryDensityActivityBase a b c0) lam *
        N^2 * Real.exp (shrunkDensityExponent a b M*(M : ℝ)) := by
  have ht : 0 ≤ (M : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg M)
  have hap : 0 < a+(M : ℝ)⁻¹ := by linarith
  have hab : a < b := by linarith
  have hd0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have hN0 : 0 ≤ N := by linarith
  have hB : 0 ≤ uniformOrdinaryDensityActivityBase a b c0 := by
    apply mul_nonneg <;> positivity
  have hbB := ordinaryDensityActivityBase_shrunk_le ha ht hshrink htau
  have he := exteriorTau_shrunk M ha hshrink
  simp only [← one_div] at hbB he
  have hℓ : 0 ≤ N*Real.exp (-c0*(D : ℝ)) := by positivity
  have hscale {t : ℝ} (h : t ≤ c0) : Real.exp ((D:ℝ)*t)*(N*Real.exp (-c0*(D:ℝ))) ≤ N := by
    rw [mul_left_comm, ← Real.exp_add]
    exact mul_le_of_le_one_right hN0 (Real.exp_le_one_iff.mpr (by nlinarith))
  have hsingle : (D : ℝ)*Real.exp ((D : ℝ)*shrunkDensityExponent a b M) ≤ N := by
    apply (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith :
      (D : ℝ)*shrunkDensityExponent a b M ≤ c0*(D : ℝ))) hd0).trans hDN
  have hpair := source_pair_coarse_scale_le (D := (D : ℝ)) (N := N) hd0 hc0 htau
  have hh := sourceRows_activity_bound (k := k) (M := M) (q := q) hd hD
    (a+1/(M : ℝ)) (b-1/(M : ℝ)) C lam (N*Real.exp (-c0*(D : ℝ))) N μ
    (uniformOrdinaryDensityActivityBase a b c0) q1 q2 (by simpa only [one_div] using hap) (by simpa only [one_div] using hshrink) hℓ (by simpa using hscale (show 0 ≤ c0 by linarith)) hN hμ hbase1 hB hbB
    hq1 hq2 hq1h hq21 hsmall (by simpa only [he] using hscale htau)
    (by simpa only [he] using hsingle)
    (by simpa only [he, mul_comm (D:ℝ) (shrunkDensityExponent a b M)] using hpair)
  simpa only [he, mul_comm (M : ℝ) (shrunkDensityExponent a b M)] using hh

end NearlyMinimax
