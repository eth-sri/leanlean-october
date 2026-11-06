module

public import NearlyMinimax.SourceRowActivity
public import NearlyMinimax.FinePairRowActivity
public import NearlyMinimax.HighActivitySummation
public import NearlyMinimax.HigherBandActivityConversion
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Summation of the actual selected higher rows under elementary source
scale inequalities. All component cap estimates come from actual measures. -/
𝚫
𝚪
𝚨
𝚩
𝚱
𝚬

𝗇 𝔍 𝘩₂
𝗃 𝔚 0 ≤ ἀ
𝗇 𝔟 q^𝘑₁
theorem finite_activity_fin_tail_le (hK : 𝔚 K) (hq : 𝔚 q)
    (hqh : q ≤ 𝙖) m (B : Fin m → ℝ)
    (hB : ∀ j, B j ≤ K*q^𝔍) :
     ∑ j, B j ≤ 2*K*q := by
  calc
    _ ≤ ∑ j : Fin m, K*q^𝔍 := Finset.sum_le_sum fun j _ => hB j
    _ = K * ∑ j : Fin m, q^𝔍 := 𝘟₂
    _ = K * ∑ j ∈ Finset.range m, 𝔟 := congrArg (fun t => K*t) $ Fin.sum_univ_eq_sum_range (fun j => 𝔟) m
    _ ≤ K*(2*q) := mul_le_mul_of_nonneg_left (finite_geometric_tail_le_two_mul hq hqh m) hK
    𝘿 := 𝖢₃

𝗇 𝔄 exteriorTau 𝖬
𝗇 𝔅 𝘵
𝗇 𝔡 higherBandInterpolationBase d lam
𝗇 𝔇 higherBandGeometricPrefactor B 𝔡 $ sourceResponseCost q C
𝗇 𝔈 higherBandGeometricConstant B 𝔡
𝗇 𝔊 𝙳
𝗃 𝔣 ἀ d D M q a b C lam ℓ N μ
𝗇 𝔗 𝔣 higherBandCoarseActivity
𝗇 𝔎 𝔗 j
𝗇 𝔏 𝘔
𝗇 𝔑 μ*𝔅
𝗇 𝔒 higherBandTargetScale d 𝔊 N μ
𝗇 𝔓 Real.exp $ D*𝔄
𝗇 𝔖 higherBandGeometricRatio d D 𝔈 𝔅 𝔑
𝗇 𝔛 ordinaryDensityActivityBase a b ≤ B
theorem higherBandCoarseActivity_geometric_le (hd : 𝗆) (hD : 𝗮)
    a b C lam ℓ N μ B (ha : 𝙆) (hab : 𝙭)
    (hℓ : 𝔚 ℓ) (hN : 𝗭₁) (hμ : 𝔚 μ) (hbase1 : 𝔑 ≤ 1)
    (hB : 𝔚 B) (hbB : 𝔛) j :
    𝔎 ≤
      𝔇 *
      𝔏 * 𝔓 * (N*ℓ) *
       𝔖 1 ^𝔍 := by
  unfold higherBandCoarseActivity higherBandFilteredMass
  split_ifs with hi
  · have hmass := higherBandRowMass_le_activityCap_of_fine d 𝔊 D D q  𝖡₃  hD
      a b ha hab C lam ℓ (min ℓ 𝔒) hi.1 false 𝖢₄
    have hcap := higherBandRowActivityCap_coarse_geometric_le (r := 𝔊) (D := D) (q := q)
      hd  𝖡₃  a b C lam N μ ℓ B hN hμ hbase1 hi.1 hB hbB
    simpa [higherBandFamilyTarget, higherBandFamilyGuardDegree, higherBandFamilyUpper,
      sourceResponseCost] using hmass.trans hcap
  · have hH : 𝔚 𝔅 := by bound
    unfold higherBandGeometricPrefactor higherBandInterpolationBase higherBandGeometricRatio
      higherBandGeometricConstant sourceResponseCost
    positivity

𝗇 𝔘 𝔣 higherBandFineActivity
𝗇 𝔐 𝔘 j
𝗇 𝔔 Real.exp $ M*𝔄
𝗇 𝔢 𝘚₂
theorem higherBandFineActivity_geometric_le (hd : 𝗆) (hD : 𝗮)
    a b C lam ℓ N μ B (ha : 𝙆) (hab : 𝙭)
    (hN : 𝗭₁) (hμ : 𝔚 μ) (hbase1 : 𝔑 ≤ 1)
    (hB : 𝔚 B) (hbB : 𝔛) j :
    𝔐 ≤
      𝔇 *
      𝔏 * 𝔔 * 𝔢 *
       𝔖 2 ^𝔍 := by
  unfold higherBandFineActivity higherBandFilteredMass
  split_ifs with hi
  · have hLT : ℓ ≤ 𝔒 := by
      simpa [higherBandFamilyTarget] using (hi.2.1 rfl).le
    have hmass := higherBandRowMass_le_activityCap_of_fine d 𝔊 M D q  𝖡₃  hD
      a b ha hab C lam ℓ 𝔒 hi.1 true 𝖧₄
    have hcap := higherBandRowActivityCap_fine_geometric_le (r := 𝔊) (M := M) (D := D) (q := q)
      hd  𝖡₃  a b C lam N μ B hN hμ hbase1 hi.1 hB hbB
    simpa [higherBandFamilyTarget, higherBandFamilyGuardDegree, higherBandFamilyUpper,
      sourceResponseCost] using hmass.trans hcap
  · have hH : 𝔚 𝔅 := by bound
    unfold higherBandGeometricPrefactor higherBandInterpolationBase higherBandGeometricRatio
      higherBandGeometricConstant sourceResponseCost
    positivity

𝗇 𝔉 2*K*𝔢
𝗃 𝔙 ἀ (M := M) (q := q) hd hD a b C lam ℓ N μ B ha hab
𝗇 𝔜 2*K*N
𝗇 𝔞 𝔉*EM
𝗇 𝔠 𝘐
/-- The entire actual selected higher family obeys the paper's geometric
activity estimate. Only elementary inequalities on the computed source scales
are inputs; every component measure estimate is derived above. -/
theorem higherBandFamily_activity_bound (hd : 𝗆) (hD : 𝗮)
    a b C lam ℓ N μ B q1 q2 (ha : 𝙆) (hab : 𝙭)
    (hℓ : 𝔚 ℓ) (hN : 𝗭₁) (hμ : 𝔚 μ) (hbase1 : 𝔑 ≤ 1)
    (hB : 𝔚 B) (hbB : 𝔛)
    (hq1 : q1 = 𝔖 1)
    (hq2 : q2 = 𝔖 2)
    (hq1h : q1 ≤ 𝙖) (hq21 : q2 ≤ q1) (hsmall : 𝔏*q1 ≤ 1)
    (hcoarse : 𝔓*ℓ ≤ N) :
    highRowTotalMass (higherBandFamilyData d k D M q a b C lam ℓ N μ).rowMass ≤
      4 * 𝔇 *
        𝔢 * 𝔔 := by
  let K := 𝔇
  let ED := 𝔓
  let EM := 𝔔
  have hK : 𝔚 K := by
    dsimp [K, higherBandGeometricPrefactor, higherBandInterpolationBase, sourceResponseCost]
    positivity
  have hH : 𝔚 𝔅 := by linarith [Real.log_nonneg hN]
  have hq10 : 𝔚 q1 := by rw [hq1]; unfold higherBandGeometricRatio higherBandGeometricConstant higherBandInterpolationBase; positivity
  have hτ : 𝔚 𝔄 := by
    apply exteriorTau_nonneg
    apply (le_div_iff₀ $ sub_pos.mpr hab ).mpr
    linarith
  have hEM := Real.one_le_exp $ mul_nonneg (Nat.cast_nonneg M) hτ
  have hc := finite_activity_fin_tail_le (K := K*𝔏*ED*N*ℓ)  𝖠₃ 
    hq10 hq1h 𝔠 𝔗 fun j => by
      have hh := 𝔙 higherBandCoarseActivity_geometric_le hℓ hN hμ hbase1 hB hbB j
      simpa only [← hq1, K, ED, mul_assoc] using hh
  have hf := finite_activity_fin_tail_le (K := K*𝔏*EM*𝔢)  𝖠₃ 
    (by rw [hq2]; unfold higherBandGeometricRatio higherBandGeometricConstant higherBandInterpolationBase; positivity) (hq21.trans hq1h) 𝔠 𝔘 fun j => by
      simpa only [← hq2, K, EM] using 𝔙 higherBandFineActivity_geometric_le hN hμ hbase1 hB hbB j
  have hc' : ∑ j, 𝔎 ≤ 𝔉 := by
    apply hc.trans
    calc
      _ = 𝔜*(ED*ℓ)*(𝔏*q1) := 𝖢₃
      _ ≤ 𝔜*N*1 := mul_le_mul (mul_le_mul_of_nonneg_left hcoarse 𝖠₃ )
        hsmall  𝖠₃  𝖠₃
      𝘿 := 𝖢₃
  have hf' : ∑ j, 𝔐 ≤ 𝔞 := by
    apply hf.trans
    calc
      _ = 𝔞*(𝔏*q2) := 𝖢₃
      _ ≤ 𝔞*1 := mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left hq21 $ sq_nonneg _ ).trans hsmall) 𝖠₃
      𝘿 := mul_one _
  rw [higherBandFamily_totalMass_eq]
  nlinarith only [hc', hf', mul_le_mul_of_nonneg_left hEM (by positivity : 𝔚 𝔉) ]
