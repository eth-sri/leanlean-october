module

public import NearlyMinimax.HigherBandFamily
public import NearlyMinimax.LowerActivityHierarchy
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Fixed geometric-ratio conversion of the genuine higher-band activation
caps. Density and interpolation constants are chosen before the degree and
sample size; no final activity estimate is assumed. -/
open MeasureTheory Filter
𝚶
𝚨
𝚩
𝚱

𝗇 𝔊 𝙊
𝗃 𝔪 ἀ^2
def higherBandInterpolationBase (d : ℕ) (lam : ℝ) : ℝ := 1024 * |lam| *𝔪 𝔊

𝗃 𝔭 1+ἀ
𝗇 𝔎 𝔭 B
𝗇 𝔏 𝔭 Ci
def higherBandGeometricConstant (B Ci : ℝ) : ℝ := 2*𝔎*𝔏
def higherBandGeometricPrefactor (B Ci Rsp : ℝ) : ℝ := 8*Rsp*𝔪 𝔎*𝔏
𝗃 𝔮 base^(ἀ/𝔊)
def higherBandGeometricRatio (d D : ℕ) (Cact H base a : ℝ) : ℝ :=
  Cact*𝚝₁*H*𝔮 a

𝗇 𝔄 r-2
𝗇 𝔓 r-1
𝗇 𝔖 𝙉
𝗇 𝔘 𝘠₁
𝗃 𝔜 0 ≤ ἀ
theorem higher_band_coefficient_absorption {r : ℕ} (hr : 𝔘) {b B Ci }
    (hb : 𝔜 b) (hB : 𝔜 B) (hCi : 𝔜 Ci) (hbB : b ≤ B) :
    b^r * Ci^𝔓 * (2*r) ≤
       8*𝔪 𝔎*𝔏 * higherBandGeometricConstant B Ci ^𝔄 := by
  have hrEq : r = 𝔄+2 := 𝖡₃
  have hrEq1 : 𝔓 = 𝔄+1 := 𝖡₃
  have hbpow : b^r ≤ 𝔪 𝔎*𝔎^𝔄 := by
    calc b^r ≤ 𝔎^r := pow_le_pow_left₀ hb  𝖡₄  r
         𝘿 := 𝖤₃
  have hcipow : Ci^𝔓 ≤ 𝔏*𝔏^𝔄 := by
    calc Ci^𝔓 ≤ 𝔏^𝔓 := pow_le_pow_left₀ hCi  𝖡₄  _
         𝘿 := 𝖤₃
  have hrpow : r ≤ 𝔖^r := by exact_mod_cast (Nat.lt_two_pow_self).le
  have hrcoef : 2*r ≤ 8*𝔖^𝔄 := by
    have he : 2^r = 4*𝔖^𝔄 := 𝖤₃
    linarith
  have h := mul_le_mul (mul_le_mul hbpow hcipow  𝖠₃  𝖠₃ ) hrcoef
     𝖠₃  𝖠₃
  apply h.trans_eq
  unfold higherBandGeometricConstant
  rw [mul_pow, mul_pow]
  ring

𝗃 𝔬 1+Real.log ἀ
𝗇 𝔅 mu*𝔬 N
𝗇 𝔇 higherBandTargetScale d r N mu
𝗇 𝔨 1/𝔊
𝗇 𝔛 𝔅^𝔨
theorem higherBandTargetScale_eq (hr : 𝔘) N mu
    (hbase : 𝔜 𝔅) :
    𝔇 =
      N*𝔛^𝔄 := by
  unfold higherBandTargetScale
  have he : 𝔄/d = 𝔨*(𝔄 : ℕ) := by
    rw [Nat.cast_sub hr]
    ring
  rw [he, Real.rpow_mul_natCast hbase]

𝗇 𝔩 𝘅
𝗇 𝔈 exteriorTau $ 𝗓₁/𝔩
𝗇 𝔉 higherBandInterpolationBase d lam
𝗇 𝔐 Fin 𝖵
𝗇 𝔑 2*𝔪 C
𝗇 𝔚 higherBandGeometricConstant B 𝔉
𝗃 𝔞 higherBandRowActivityCap d r ἀ D q a b C lam
𝗇 𝔠 ordinaryDensityActivityBase a b ≤ B
𝗇 𝔢 𝘐₁
𝗇 𝔣 𝔪 D
𝗇 𝔤 m*𝔈
𝗇 𝔥 higherBandGeometricRatio d D 𝔚
/-- A generic true cap is a geometric-ratio row bound once its T² and
logarithmic scale are bounded by the actual target powers. -/
theorem higherBandRowActivityCap_geometric_le {d r m D q : ℕ} (hr : 𝔘)
    a b C lam T B H base P alpha (hT : 𝖹) (hB : 𝔜 B)
    (hbase : 𝔜 base) (hP : 𝔜 P) (_hH : 𝔜 H)
    (hbB : 𝔠)
    (hlog : 𝔬 T ≤ H)
    (hT2 : 𝔪 T ≤ P*𝔮 alpha^𝔄) :
    𝔞 m T ≤
      higherBandGeometricPrefactor B 𝔉
        ((∑ h : 𝔐, |𝔢|)*𝔑) *
      𝔣 * Real.exp 𝔤 * P *
       𝔥 H base alpha ^𝔄 := by
  have hCi : 𝔜 𝔉 := by unfold higherBandInterpolationBase; positivity
  have hcoef := higher_band_coefficient_absorption hr (by unfold ordinaryDensityActivityBase; positivity) hB hCi hbB
  have hlog0 : 0 ≤ 𝔬 T := 𝖥₄
  have hCact : 𝔜 𝔚 := by
    unfold higherBandGeometricConstant
    positivity
  have hDpower : D^r = 𝔣*𝚝₁^𝔄 := by
    nth_rw 1 [show r=𝔄+2 by omega]
    ring
  have hscale := mul_le_mul hT2 (pow_le_pow_left₀ hlog0 hlog 𝔄)  𝖠₃  𝖠₃
  have h := mul_le_mul hcoef hscale (by positivity) $ by positivity
  have hh := mul_le_mul_of_nonneg_left h
    $ show 0 ≤ D^r * Real.exp 𝔤 *
      ((∑ h : 𝔐, |𝔢|)*𝔑) by positivity
  convert hh using 1 <;>
    simp only [higherBandRowActivityCap, higherBandInterpolationCap, higherBandGeometricPrefactor,
      higherBandGeometricRatio, higherBandInterpolationBase, hDpower] <;> ring

𝗇 𝔔 𝔬 N
𝗇 𝔦 mul_nonneg hmu hH
theorem higherBandTargetScale_le_N (_hd : 𝗆) (hr : 𝔘)
    (hN : 𝗭₁) (hmu : 𝔜 mu) (hbase1 : 𝔅 ≤ 1) :
    𝔇 ≤ N := by
  have hH : 𝔜 𝔔 := 𝖥₄
  have hpower := Real.rpow_le_one 𝔦 hbase1
    $ show 0 ≤ 𝔄/𝔊 by
      have hrR : 𝔖 ≤ r := by exact_mod_cast hr
      positivity
  unfold higherBandTargetScale
  bound

𝗇 𝔟 higherBandRowActivityCap_geometric_le hr a b C lam _ B _ _
𝗇 𝔧 N*ell
𝗃 𝔫 ἀ ell 𝔇
/-- Actual coarse target cap, uniformly for every legal selected target. -/
theorem higherBandRowActivityCap_coarse_geometric_le (hd : 𝗆) (hr : 𝔘)
    a b C lam N mu ell B (hN : 𝗭₁) (hmu : 𝔜 mu)
    (hbase1 : 𝔅 ≤ 1)
    (hT : 1 ≤ 𝔫 min) (hB : 𝔜 B)
    (hbB : 𝔠) :
    𝔞 D 𝔫 min ≤
      higherBandGeometricPrefactor B 𝔉
        ((∑ h : 𝔐, |𝔢|)*𝔑) *
      𝔣 * Real.exp (D*𝔈) * 𝔧 *
       𝔥
        𝔔 𝔅 1 ^𝔄 := by
  have hH : 𝔜 𝔔 := 𝖥₄
  have hbase := 𝔦
  have hell : 𝔜 ell := 𝖤₃
  have hnu := higherBandTargetScale_le_N hd hr hN hmu hbase1
  apply 𝔟 𝔧 1 hT hB hbase  𝖠₃  hH hbB
  · exact add_le_add_right (Real.log_le_log  𝖡₄  $ (min_le_right ..).trans hnu ) 1
  · have h := mul_le_mul 𝔫 min_le_left
      𝔫 min_le_right  𝖡₄  hell
    calc
      _ ≤ ell * 𝔇 := 𝖡₄
      𝘿 := by rw [higherBandTargetScale_eq hr N mu hbase]; ring

/-- Actual fine target cap with the exact q2 power, uniformly over all legal selected targets. -/
theorem higherBandRowActivityCap_fine_geometric_le (hd : 𝗆) (hr : 𝔘)
    a b C lam N mu B (hN : 𝗭₁) (hmu : 𝔜 mu)
    (hbase1 : 𝔅 ≤ 1) (hT : 1 ≤ 𝔇)
    (hB : 𝔜 B) (hbB : 𝔠) :
    𝔞 M 𝔇 ≤
      higherBandGeometricPrefactor B 𝔉
        ((∑ h : 𝔐, |𝔢|)*𝔑) *
      𝔣 * Real.exp (M*𝔈) * 𝔪 N *
       𝔥
        𝔔 𝔅 2 ^𝔄 := by
  have hH : 𝔜 𝔔 := 𝖥₄
  have hbase := 𝔦
  have hnu := higherBandTargetScale_le_N hd hr hN hmu hbase1
  apply 𝔟 𝔪 N 2 hT hB hbase  𝖠₃  hH hbB
  · bound
  · rw [higherBandTargetScale_eq hr N mu hbase, mul_pow]
    have he : 𝔪 𝔛 = 𝔅^(2/𝔊) := by
      rw [← Real.rpow_mul_natCast hbase]
      ring
    rw [← pow_mul, Nat.mul_comm 𝔄 2, pow_mul, he]

𝗇 𝔍 𝔩/a
𝗇 𝔙 div_pos (sub_pos.mpr hab) ha
/-- Exact elementary density-base simplification, including the true exterior interval exponent. -/
theorem ordinaryDensityActivityBase_eq (ha : 𝙆) (hab : 𝙭) :
    ordinaryDensityActivityBase a b = Real.exp 𝔭 𝘦₂*𝔍 := by
  have he : 𝘸₁ = -𝔍 := by
    unfold densityMargin
    grind
  unfold ordinaryDensityActivityBase
  rw [he, abs_neg, abs_of_pos 𝔙, exteriorTau_sqrt_ratio a b ha hab]
  rfl

def uniformOrdinaryDensityActivityBase (a b c0 : ℝ) : ℝ :=
  Real.exp 𝔭 c0*𝔍

𝗇 𝔒 a+t
𝗇 𝔗 b-t
𝗇 𝔡 uniformOrdinaryDensityActivityBase a b c0
/-- One fixed density base bounds every legal shrunk interval with tauM<=c0. -/
theorem ordinaryDensityActivityBase_shrunk_le
    (ha : 𝙆) (ht : 𝔜 t) (hshrink : 𝔒 < 𝔗)
    (htau : densityIntervalExponent 𝔒 𝔗 ≤ c0) :
    ordinaryDensityActivityBase 𝔒 𝔗 ≤ 𝔡 := by
  have hap : 0 < 𝔒 := 𝖡₄
  rw [ordinaryDensityActivityBase_eq hap hshrink]
  have hratio : (𝔗-𝔒)/𝔒 ≤ 𝔍 := by
    bound
  exact mul_le_mul (Real.exp_le_exp.mpr 𝖡₄ ) hratio
    (div_pos (sub_pos.mpr hshrink) hap).le 𝙫

def higherBandSourceCact (d : ℕ) (a b c0 lam : ℝ) : ℝ :=
  higherBandGeometricConstant 𝔡 𝔉

theorem higherBandSourceCact_positive d (ha : 𝙆) (hab : 𝙭) :
    0 < higherBandSourceCact d a b c0 lam := by
  have hB : 0 < 𝔡 :=
    mul_pos (Real.exp_pos _) 𝔙
  unfold higherBandSourceCact higherBandGeometricConstant higherBandInterpolationBase
  positivity
