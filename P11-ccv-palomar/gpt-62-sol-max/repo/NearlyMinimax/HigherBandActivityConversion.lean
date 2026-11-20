module

public import NearlyMinimax.HigherBandFamily
public import NearlyMinimax.LowerActivityHierarchy

@[expose] public section

/-! Fixed geometric-ratio conversion of the genuine higher-band activation
caps. Density and interpolation constants are chosen before the degree and
sample size; no final activity estimate is assumed. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def higherBandGeometricConstant (B Ci : ℝ) : ℝ := 2*(1+B)*(1+Ci)
def higherBandGeometricPrefactor (B Ci Rsp : ℝ) : ℝ := 8*Rsp*(1+B)^2*(1+Ci)
def higherBandGeometricRatio (d D : ℕ) (Cact H base a : ℝ) : ℝ :=
  Cact*(D : ℝ)*H*base^(a/(d : ℝ))

theorem higher_band_coefficient_absorption {r : ℕ} (hr : 2 ≤ r) {b B Ci : ℝ}
    (hb : 0 ≤ b) (hB : 0 ≤ B) (hCi : 0 ≤ Ci) (hbB : b ≤ B) :
    b^r * Ci^(r-1) * (2*(r : ℝ)) ≤
      (8*(1+B)^2*(1+Ci)) * (higherBandGeometricConstant B Ci)^(r-2) := by
  have hrEq : r = (r-2)+2 := by omega
  have hrEq1 : r-1 = (r-2)+1 := by omega
  have hbpow : b^r ≤ (1+B)^2*(1+B)^(r-2) := by
    calc b^r ≤ (1+B)^r := pow_le_pow_left₀ hb (by linarith) r
         _ = _ := by grind
  have hcipow : Ci^(r-1) ≤ (1+Ci)*(1+Ci)^(r-2) := by
    calc Ci^(r-1) ≤ (1+Ci)^(r-1) := pow_le_pow_left₀ hCi (by linarith) _
         _ = _ := by rw [hrEq1, pow_succ]; ring
  have hrpow : (r : ℝ) ≤ (2 : ℝ)^r := by exact_mod_cast (show r < 2^r from Nat.lt_two_pow_self).le
  have hrcoef : 2*(r : ℝ) ≤ 8*(2 : ℝ)^(r-2) := by
    have he : (2 : ℝ)^r = 4*(2 : ℝ)^(r-2) := by grind
    rw [he] at hrpow
    nlinarith
  have h := mul_le_mul (mul_le_mul hbpow hcipow (by positivity) (by positivity)) hrcoef
    (by positivity) (by positivity)
  apply h.trans_eq
  unfold higherBandGeometricConstant
  simp [mul_pow] <;> ring

theorem higherBandTargetScale_eq {d r : ℕ} (hr : 2 ≤ r) (N mu : ℝ)
    (hbase : 0 ≤ mu*(1+Real.log N)) :
    higherBandTargetScale d r N mu =
      N*((mu*(1+Real.log N))^(1/(d : ℝ)))^(r-2) := by
  unfold higherBandTargetScale
  congr 1
  have he : ((r : ℝ)-2)/(d : ℝ) = (1/(d : ℝ))*(r-2 : ℕ) := by
    rw [Nat.cast_sub hr]
    ring
  rw [he, Real.rpow_mul_natCast hbase]

/-- A generic true cap is a geometric-ratio row bound once its T² and
logarithmic scale are bounded by the actual target powers. -/
theorem higherBandRowActivityCap_geometric_le {d r m D q : ℕ} (hr : 2 ≤ r)
    (a b C lam T B H base P alpha : ℝ) (hT : 1 ≤ T) (hB : 0 ≤ B)
    (hbase : 0 ≤ base) (hP : 0 ≤ P)
    (hbB : ordinaryDensityActivityBase a b ≤ B)
    (hlog : 1+Real.log T ≤ H)
    (hT2 : T^2 ≤ P*(base^(alpha/(d : ℝ)))^(r-2)) :
    higherBandRowActivityCap d r m D q a b C lam T ≤
      higherBandGeometricPrefactor B (higherBandInterpolationBase d lam) (sourceResponseCost q C) *
      (D : ℝ)^2 * Real.exp ((m : ℝ)*exteriorTau ((a+b)/(b-a))) * P *
      (higherBandGeometricRatio d D (higherBandGeometricConstant B (higherBandInterpolationBase d lam)) H base alpha)^(r-2) := by
  have hb0 : 0 ≤ ordinaryDensityActivityBase a b := by unfold ordinaryDensityActivityBase; positivity
  have hCi : 0 ≤ higherBandInterpolationBase d lam := by unfold higherBandInterpolationBase; positivity
  have hcoef := higher_band_coefficient_absorption hr hb0 hB hCi hbB
  have hlog0 : 0 ≤ 1+Real.log T := by linarith [Real.log_nonneg hT]
  have hlogpow := pow_le_pow_left₀ hlog0 hlog (r-2)
  have hCact : 0 ≤ higherBandGeometricConstant B (higherBandInterpolationBase d lam) := by
    unfold higherBandGeometricConstant
    positivity
  have hDpower : (D : ℝ)^r = (D : ℝ)^2*(D : ℝ)^(r-2) := by
    nth_rw 1 [show r=(r-2)+2 by omega]
    ring
  have hscale := mul_le_mul hT2 hlogpow (by positivity) (by positivity)
  have h := mul_le_mul hcoef hscale (by positivity) (by positivity)
  have hh := mul_le_mul_of_nonneg_left h
    (show 0 ≤ (D : ℝ)^r * Real.exp ((m : ℝ)*exteriorTau ((a+b)/(b-a))) *
      sourceResponseCost q C from mul_nonneg (by positivity) (sourceResponseCost_nonneg q C))
  convert hh using 1 <;>
    simp only [higherBandRowActivityCap, higherBandInterpolationCap, cardinalSeparatedCostBound, higherBandGeometricPrefactor,
      higherBandGeometricRatio, higherBandInterpolationBase, sourceResponseCost, hDpower, mul_pow] <;> ring

/-- The geometric ratio at the actual logarithmic source scale. -/
def higherBandSourceRatio (d D : ℕ) (B lam N μ α : ℝ) : ℝ :=
  higherBandGeometricRatio d D (higherBandGeometricConstant B (higherBandInterpolationBase d lam))
    (1 + Real.log N) (μ * (1 + Real.log N)) α

theorem higherBandSourceRatio_nonneg {d D : ℕ} {B lam N μ α : ℝ}
    (hB : 0 ≤ B) (hN : 1 ≤ N) (hμ : 0 ≤ μ) : 0 ≤ higherBandSourceRatio d D B lam N μ α := by
  have hH := add_nonneg (by norm_num : (0 : ℝ) ≤ 1) (Real.log_nonneg hN)
  unfold higherBandSourceRatio higherBandGeometricRatio higherBandGeometricConstant higherBandInterpolationBase
  positivity

theorem higherBandTargetScale_le_N {d r : ℕ} (hr : 2 ≤ r) {N μ : ℝ}
    (hN : 1 ≤ N) (hbase : 0 ≤ μ*(1+Real.log N)) (hbase1 : μ*(1+Real.log N) ≤ 1) :
    higherBandTargetScale d r N μ ≤ N := by
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  unfold higherBandTargetScale
  exact mul_le_of_le_one_right (by linarith) (Real.rpow_le_one hbase hbase1 (by positivity))

/-- Exact elementary density-base simplification, including the true exterior interval exponent. -/
theorem ordinaryDensityActivityBase_eq {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ordinaryDensityActivityBase a b = Real.exp (1+densityIntervalExponent a b)*((b-a)/a) := by
  have he : b/densityMargin a b 0 = -((b-a)/a) := by
    unfold densityMargin
    grind
  unfold ordinaryDensityActivityBase
  rw [he, abs_neg, abs_of_pos (div_pos (sub_pos.mpr hab) ha), exteriorTau_sqrt_ratio a b ha hab]
  rfl

def uniformOrdinaryDensityActivityBase (a b c0 : ℝ) : ℝ :=
  Real.exp (1+c0)*((b-a)/a)

/-- One fixed density base bounds every legal shrunk interval with tauM<=c0. -/
theorem ordinaryDensityActivityBase_shrunk_le {a b t c0 : ℝ}
    (ha : 0 < a) (ht : 0 ≤ t) (hshrink : a+t < b-t)
    (htau : densityIntervalExponent (a+t) (b-t) ≤ c0) :
    ordinaryDensityActivityBase (a+t) (b-t) ≤ uniformOrdinaryDensityActivityBase a b c0 := by
  have hap : 0 < a+t := by linarith
  rw [ordinaryDensityActivityBase_eq hap hshrink]
  have hratio : ((b-t)-(a+t))/(a+t) ≤ (b-a)/a := by
    apply (div_le_div_iff₀ hap ha).mpr
    nlinarith
  exact mul_le_mul (Real.exp_le_exp.mpr (by linarith)) hratio
    (div_pos (sub_pos.mpr hshrink) hap).le (Real.exp_pos _).le

def higherBandSourceCact (d : ℕ) (a b c0 lam : ℝ) : ℝ :=
  higherBandGeometricConstant (uniformOrdinaryDensityActivityBase a b c0) (higherBandInterpolationBase d lam)

theorem higherBandSourceCact_positive (d : ℕ) {a b c0 lam : ℝ} (ha : 0 < a) (hab : a < b) :
    0 < higherBandSourceCact d a b c0 lam := by
  have hB : 0 < uniformOrdinaryDensityActivityBase a b c0 :=
    mul_pos (Real.exp_pos _) (div_pos (sub_pos.mpr hab) ha)
  unfold higherBandSourceCact higherBandGeometricConstant higherBandInterpolationBase
  positivity

end NearlyMinimax
