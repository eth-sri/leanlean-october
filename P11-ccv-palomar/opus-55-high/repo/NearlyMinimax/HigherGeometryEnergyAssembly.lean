module

public import NearlyMinimax.SpatialGeometryFactorialEnergy
public import NearlyMinimax.OrdinaryFineAliasSaddleEnvelope
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Actual higher-count envelope integration and factorial assembly. The
only intermediate ordinary-family input is its genuine finite spatial
integral sum; the canonical module derives it from the constructed bands. -/
𝚯
𝚪
𝚨
𝚩
𝚭
𝚬

𝗇 𝔄 𝖧⁻¹
𝗃 𝔦 higherBandTargetScale d ἀ N mu
𝗇 𝔔 fun t => 𝔦 t
𝗇 𝔗 𝗊₁
𝗃 𝔨 ἀ (F := D)
𝗇 𝔅 𝔨 ordinaryFineAliasFamilyResponseSquareEnvelope 𝔗 M R q aD bD c0 C a rho eta ell 𝔔 U
𝗇 𝔏 𝗾₂
𝗇 𝔐 max 1 𝔦 r
𝗇 𝔑 lt_of_lt_of_le zero_lt_one hell
𝗇 𝔒 bD-𝔄
𝗇 𝔓 aD+𝔄
𝗃 𝔧 ἀ 𝔓 𝔒 ell N M q C a rho eta U
𝗇 𝔚 𝔧 finePairAliasGeometryEnvelope
𝗇 𝔛 𝔧 fineFieldGeometryEnvelope
𝗇 𝔜 𝔨 cardinalGeometryEnvelope q 𝔒 C a rho eta
𝗃 𝔤 if M<r then ∫ U, ἀ ∂𝔏 else 0
theorem completeSourceHigherGeometryEnvelope_integral_eq [NeZero d]
    (hd : 𝘚) (hr : 𝘠₁) (aD bD c0 ell N mu : ℝ) (M R q : ℕ)
    (C a rho eta : ℝ) (hell : 𝗲₁) (hellN : ell ≤ N) :
     ∫ U, completeSourceHigherGeometryEnvelope (d := d) (n := r) (D := D)
      aD bD c0 ell N mu M R q C a rho eta U ∂𝔏 =
      4*( ∫ U, 𝔜
          𝔐 U ∂𝔏 +
        𝔤 𝔅 +
        𝔤 𝔚 +
         ∫ U, 𝔛 ∂𝔏 ) := by
  have hA := (𝔨 cardinalGeometryEnvelope_integrable_and_le hd hr q
    𝔒 C a rho eta (T := 𝔐) $ le_max_left .. ).1
  have hB := ordinaryFineAliasFamilyResponseSquareEnvelope_integrable (n := r) (F := D) hd
    𝔗 M R q aD bD c0 C a rho eta ell
    𝔔 hell fun t ht => by
      have h := (Finset.mem_filter.mp ht).2
      bound
  have hP := (finePairAliasGeometryEnvelope_integrable_and_le (d := d) (n := r)  𝖡₃ 
    𝔓 𝔒 ell N 𝔑 hellN M q C a rho eta).1
  have hF := (fineFieldGeometryEnvelope_integrable_and_le (d := d) (n := r)  𝖡₃ 
    𝔓 𝔒 ell N 𝔑 M q C a rho eta).1
  unfold completeSourceHigherGeometryEnvelope
  by_cases hMr : M<r
  · rw [integral_const_mul]
    have h1 := integral_add ((hA.add hB).add hP) hF
    have h2 := integral_add (hA.add hB) hP
    have h3 := integral_add hA hB
    simp_all
  · simp only [if_neg hMr,add_zero]
    rw [integral_const_mul,integral_add hA hF]

𝗇 𝔠 3+j
𝗇 𝔢 𝘐
𝗇 𝔇 ∑ j ∈ Finset.range 𝔢, poissonCountWeight 𝖫₂ 𝔠 * ∫ U, 𝘭 ∂fullSpatialPatchDesign d 𝔠
𝗇 𝔈 𝔠
𝗇 𝔡 𝙊
𝗇 𝔉 N^(-𝔡)
𝗇 𝔊 𝖫₂
𝗇 𝔍 3*Cs
𝗇 𝔎 Finset.range 𝔢
𝗃 𝔥 ἀ d q aD bD C a rho c0
𝗇 𝔖 𝔥 finePairSaddleAliasFactorialConstant K 𝔍
𝗇 𝔘 𝔥 finePairFieldFactorialConstant 𝔍
𝗇 𝔙 (𝔓+𝔒)/ (𝔒-𝔓)
𝗇 𝔞 𝖦₁+j
𝗇 𝔟 𝗸
theorem finite_complete_higher_geometry_energy_le {d D : ℕ} [NeZero d]
    (hd : 𝘚) (hD : 𝗕) aD bD c0 K ell N mu (M R q : ℕ)
    C a rho eta Cs Eord (haD : 𝘗₂) (ha : 𝙆)
    (hshrink : 𝔓 < 𝔒)
    (htau : exteriorTau 𝔙 ≤ c0)
    (hc0 : 0 ≤ c0) (hK : 𝖭₂) (hCs : 0 ≤ Cs)
    (hell : 𝗲₁) (hellN : ell ≤ N) (hcut : ell=𝗐)
    (hDM : 𝚝₁ ≤ K*M) (hmu : 0 < mu) (hmu1 : 𝗦₁)
    (hmuH : mu*𝘵 ≤ 1) (hTaylor : 𝘅₁)
    (hfield : Real.exp (2*exteriorTau 𝔙*M) * (ell^(2-𝔡))^2 * mu^4 ≤
        𝙺₁*𝔉)
    (hord : ∑ j ∈ Finset.range 𝘀₂, poissonCountWeight 𝔊 𝔞 *
      ∫ U, 𝔅 ∂fullSpatialPatchDesign d 𝔞 ≤ Eord) :
    𝔇 ≤
      4*(cardinalGeometryFactorialConstant d q bD C a rho Cs*𝔟*𝔉*𝙺₁ + Eord +
        𝔖 *
          (𝔟*N^(4-𝔡)) *
          poissonCountWeight (𝔖*mu) 𝖦₁ +
        𝔘*𝔟*𝙺₁*𝔉) := by
  have hN := hell.trans hellN
  have had : aD ≤ 𝔓 := le_add_of_nonneg_right
    $ inv_nonneg.mpr $ Nat.cast_nonneg M
  have hbd : 𝔒 ≤ bD := 𝖡₄
  have hbd0 := (haD.trans_le had).le.trans hshrink.le
  have hA := finite_cardinal_geometry_budget_le (D := D) (F := D) hd hbd0 hbd q C a rho eta Cs ha hCs hN hmu hmu1 hmuH hTaylor
  have hP := finite_fine_pair_alias_geometry_budget_le hd haD had hbd hshrink htau hc0 hK M q
    C a rho eta ell N Cs mu (lt_of_lt_of_le zero_lt_one hN) hcut hell hellN hDM hCs hmu.le hmu1
  have hF := finite_fine_field_geometry_budget_le hd hD haD had hbd hshrink htau M q C a rho eta
    ell N Cs mu 𝔑 hCs hmu.le hmu1
  have hFconst : 0 ≤ 𝔘 := by
    unfold finePairFieldFactorialConstant fieldTailConstant
    have hPre := 𝔥 finePairUniformSpatialPrefactor_nonneg
    have hP4 := poissonCountWeight_nonneg (by positivity [finePairFieldGeometricBase_nonneg d bD] :
      0 ≤ 𝔍*(finePairFieldGeometricBase d bD*2^12)) 4
    positivity
  have hFs := mul_le_mul_of_nonneg_left hfield
    $ mul_nonneg hFconst (by positivity : 0 ≤ 𝔟)
  let f := fun r => poissonCountWeight 𝔊 r *
    ∫ U, 𝔅 ∂𝔏
  have hf r : 0 ≤ f r := mul_nonneg (poissonCountWeight_nonneg (mul_nonneg hCs hmu.le) r)
    $ integral_nonneg fun U => ordinaryFineAliasFamilyResponseSquareEnvelope_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ U
  have hO := (finite_refined_gated_sum_le_tail D M f hf).trans hord
  have heq : 𝔇 =
      4*( ∑ j ∈ 𝔎, poissonCountWeight 𝔊 𝔈 *
        ∫ U, 𝔜
          (max 1 𝔦 𝔈) U ∂fullSpatialPatchDesign d 𝔈 +
        (∑ j ∈ 𝔎, if M<𝔈 then f 𝔈 else 0) +
        (∑ j ∈ 𝔎, poissonCountWeight 𝔊 𝔈 *
           if M<𝔈 then ∫ U, 𝔚 ∂fullSpatialPatchDesign d 𝔈 else 0 ) +
         ∑ j ∈ 𝔎, poissonCountWeight 𝔊 𝔈 *
          ∫ U, 𝔛 ∂fullSpatialPatchDesign d 𝔈 ) := by
    have hInt j := completeSourceHigherGeometryEnvelope_integral_eq (r := 𝔈) (D := D)
      hd  𝖡₃  aD bD c0 ell N mu M R q C a rho eta hell hellN
    simp_rw [hInt]
    try dsimp [f]
    have halg (w A B P F : ℝ) : w*(4*(A+B+P+F))=4*(w*A+w*B+w*P+w*F) := 𝖢₃
    simp_rw [halg,mul_ite,mul_zero]
    rw [←Finset.mul_sum]
    simp only [Finset.sum_add_distrib]
  linarith
