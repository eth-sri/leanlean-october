module

public import NearlyMinimax.SourceTotalActivity
public import NearlyMinimax.SourcePairActivityConversion
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! The complete source activity bound at the actual common cutoff and
actual shrunk density interval. Its constant is fixed before M and N. -/
𝚫
𝚪
𝚨
𝚩
𝚱

𝗇 𝔒 𝖧
𝗇 𝔄 𝔒⁻¹
𝗇 𝔅 𝚝₁
𝗇 𝔇 𝙉₂ M
𝗇 𝔏 𝘵
𝗇 𝔈 higherBandGeometricRatio d D (higherBandSourceCact d a b c0 lam) 𝔏 $ μ*𝔏
𝗇 𝔉 uniformOrdinaryDensityActivityBase a b c0
𝗇 𝔊 N*Real.exp (-c0*𝔅)
𝗇 𝔍 a+𝔄
𝗇 𝔎 b-𝔄
𝗇 𝔐 c0*𝔅
𝗇 𝔑 𝔅*𝔇
theorem sourceRows_shrunk_activity_bound {d k D M q : ℕ} [NeZero d] (hd : 𝗆) (hD : 𝗮)
    (a b C lam N μ c0 q1 q2 : ℝ) (ha : 𝙆)
    (hshrink : 𝔍 < 𝔎) (htau : 𝔇 ≤ c0)
    (hc0 : 1 ≤ c0) (hN : 𝗭₁) (hμ : 0 ≤ μ) (hbase1 : μ*𝔏 ≤ 1)
    (hDN : 𝔅*Real.exp 𝔐 ≤ N)
    (hq1 : q1 = 𝔈 1)
    (hq2 : q2 = 𝔈 2)
    (hq1h : q1 ≤ 𝙖) (hq21 : q2 ≤ q1) (hsmall : 𝔅^2*q1 ≤ 1) :
    highRowTotalMass (𝙴₂ 𝔍 𝔎 C lam
      𝔊 N μ).rowMass ≤
      sourceActivityConstant d q C 𝔉 lam *
        𝘚₂ * Real.exp (𝔇*𝔒) := by
  have ht : 0 ≤ 𝔄 := inv_nonneg.mpr $ Nat.cast_nonneg M
  have hap : 0 < 𝔍 := 𝖡₄
  have hab : 𝙭 := 𝖡₄
  have hd0 : 𝙋 ≤ D := Nat.cast_nonneg D
  have hN0 : 0 ≤ N := 𝖡₄
  have hB : 0 ≤ 𝔉 := by
    unfold uniformOrdinaryDensityActivityBase
    exact mul_nonneg 𝙫 $ div_nonneg (sub_pos.mpr hab).le ha.le
  have hbB := ordinaryDensityActivityBase_shrunk_le ha ht hshrink htau
  have he : exteriorTau ((𝔍+𝔎)/(𝔎-𝔍)) =
      𝔇 := by
    rw [exteriorTau_sqrt_ratio _ _ hap hshrink]
    rfl
  have hℓN : 𝔊 ≤ N := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr 𝖥₃ ) hN0
  have hsingle : 𝔅*Real.exp 𝔑 ≤ N := by
    apply (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr $ by nlinarith ) hd0).trans hDN
  have hpair := source_pair_coarse_scale_le (N := N) hd0 hc0 htau
  have hcoarse : Real.exp 𝔑*𝔊 ≤ N := by
    have h := mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr $ mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr htau) hd0 ) hN0
    calc
      _ = N*Real.exp ((𝔇-c0)*𝔅) := by
        rw [sub_mul, Real.exp_sub]
        rw [show -c0*𝔅 = -𝔐 by ring, Real.exp_neg,
          mul_comm 𝔅 𝔇]
        ring
      _ ≤ N := by simpa only [mul_one] using h
  have hh := sourceRows_activity_bound (k := k) (M := M) (q := q) hd hD
    𝔍 𝔎 C lam 𝔊 N μ
    𝔉 q1 q2 hap hshrink  𝖠₃  hℓN hN hμ hbase1 hB hbB
    hq1 hq2 hq1h hq21 hsmall (by simpa only [he] using hcoarse)
    (by simpa only [he] using hsingle)
    $ by simpa only [he, mul_comm 𝔅 𝔇] using hpair
  simpa only [he, mul_comm 𝔒 𝔇] using hh
