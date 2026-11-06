module

public import NearlyMinimax.CardinalFactorialEnergy
public import NearlyMinimax.HighSpatialEnvelopes
public import NearlyMinimax.HigherBandFamily
public import NearlyMinimax.FiniteCountEnergyAssembly
public import NearlyMinimax.FinePairSaddleFactorialEnergy
public import NearlyMinimax.HighCompleteGeometry
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Factorial integration of the genuine deterministic spatial envelopes.
All constants in these bounds precede the count and cutoff quantifiers. -/
𝚯
𝚪
𝚨
𝚩
𝚱

theorem poissonCountWeight_mul_pow x a r :
    poissonCountWeight x r * a^r = poissonCountWeight (a*x) r := by
  unfold poissonCountWeight
  ring

𝗇 𝔇 matchedCardinalTargetCutoff d (r-2) N mu
𝗃 𝔛 max 1 $ higherBandTargetScale d ἀ N mu
theorem higherBandTargetScale_max_eq_matched (hr : 𝘠₁) N mu :
    𝔛 r = 𝔇 := by
  unfold higherBandTargetScale matchedCardinalTargetCutoff
  simp_all

𝗇 𝔅 3*Cs
def cardinalGeometryFactorialConstant (d q : ℕ) (B C a rho Cs : ℝ) : ℝ :=
  cardinalInterpolationFactorialConstant d B a 𝔅 +
    cardinalTaylorFactorialConstant d q B C a rho 𝔅

𝗇 𝔄 3+j
𝗇 𝔈 Finset.range 𝘐
𝗇 𝔉 𝖫₂
𝗇 𝔘 𝔛 𝔄
𝗇 𝔑 ∑ j ∈ 𝔈, poissonCountWeight 𝔉 𝔄 * ∫ U, cardinalGeometryEnvelope (F := F) q bd C a rho eta 𝔘 U ∂fullSpatialPatchDesign d 𝔄
𝗇 𝔓 𝔅*mu
𝗇 𝔖 𝙊
𝗇 𝔗 D-1
𝗃 𝔙 0 ≤ ἀ
theorem finite_cardinal_geometry_budget_le (hd : 𝘚)
    (hbd : 𝔙 bd) (hbdB : bd ≤ B) q C a rho eta Cs
    (ha : 𝙆) (hCs : 𝔙 Cs) (hN : 𝗭₁) (hmu : 0 < mu)
    (hmu1 : 𝗦₁) (hmuH : mu*𝘵 ≤ 1)
    (hTaylor : 𝘅₁) :
    𝔑 ≤
      cardinalGeometryFactorialConstant d q B C a rho Cs * 𝗸*N^(-𝔖)*𝙺₁ := by
  let f := fun r => poissonCountWeight 𝔓 r *
    (cardinalAliasSpatialComponent d r bd a eta 𝔇 +
      cardinalTaylorSpatialComponent d r q bd C a rho eta)
  have hf r : 0 ≤ f r := by
    dsimp [f]
    have h := poissonCountWeight_nonneg (by positivity : 𝔙 𝔓) r
    have hb : 0 ≤ cardinalDefectSquareBudget d r 𝔇 := by
      have hT : 1 ≤ 𝔇 := le_max_left ..
      have hlog : 0 ≤ 1+Real.log 𝔇 := by
        bound
      unfold cardinalDefectSquareBudget
      unfold spatialUnaryIntegralConstant
      positivity
    unfold cardinalAliasSpatialComponent cardinalTaylorSpatialComponent
      cardinalRawAliasCoefficient cardinalRawTaylorCoefficient spatialScaleIntegralConstant
    positivity
  have hmajor : 𝔑 ≤
        ∑ j ∈ 𝔈, f 𝔄 := by
    apply Finset.sum_le_sum
    intro j _
    have hi := (cardinalGeometryEnvelope_integrable_and_le (n := 𝔄) (F := F)
      hd  𝖡₃  q bd C a rho eta (T := 𝔘)
        $ le_max_left .. ).2
    have h := mul_le_mul_of_nonneg_left hi $ poissonCountWeight_nonneg (by positivity : 𝔙 𝔉) 𝔄
    rw [cardinalRawSpatialEnergyBudget_split, higherBandTargetScale_max_eq_matched 𝖡₃ ] at h
    rw [higherBandTargetScale_max_eq_matched 𝖡₃ ]
    convert h using 1
    try dsimp [f]
    rw [← mul_assoc, poissonCountWeight_mul_pow]
    ring
  apply (hmajor.trans $ finite_refined_sum_le_start_two D f hf ).trans
  dsimp [f]
  simp_rw [show ∀ j , 2+j-2=j from fun j => 𝖡₃, mul_add]
  rw [Finset.sum_add_distrib]
  have hA := finite_cardinal_interpolation_budget_le hbd hbdB (by omega : 𝗆)
    𝔗 a eta 𝔅 ha  𝖠₃  hN hmu hmuH
  have hT := finite_cardinal_taylor_budget_le hbd hbdB d q 𝔗 C a rho eta 𝔅
     𝖠₃  (lt_of_lt_of_le zero_lt_one hN) hmu.le hmu1 hTaylor
  exact (add_le_add hA hT).trans_eq $ by unfold cardinalGeometryFactorialConstant; ring

𝗇 𝔊 exteriorTau 𝙻
𝗇 𝔍 4+j
𝗃 𝔚 ἀ ad bd ell N M q C a rho eta U
𝗇 𝔎 𝔚 fineFieldGeometryEnvelope
𝗇 𝔐 D-3
𝗃 𝔜 ἀ d q aD bD C a rho c0
theorem finite_fine_field_geometry_budget_le [NeZero d] (hd : 𝘚) (hD : 𝗕)
    (haD : 𝘗₂) (had : aD ≤ ad) (hbd : bd ≤ bD)
    (hab : 𝖽) (htau : 𝔊 ≤ c0)
    M q C a rho eta ell N Cs mu (hell : 𝚁₁)
    (hCs : 𝔙 Cs) (hmu : 𝔙 mu) (hmu1 : 𝗦₁) :
     ∑ j ∈ 𝔈, poissonCountWeight 𝔉 𝔄 *
      ∫ U, 𝔎
        ∂fullSpatialPatchDesign d 𝔄 ≤
      𝔜 finePairFieldFactorialConstant 𝔅 * 𝗸 *
        Real.exp (2*𝔊*M) * (ell^(2-𝔖))^2 * mu^4 := by
  let f := fun r => poissonCountWeight 𝔉 r *
    ∫ U, 𝔎
      ∂𝗾₂
  have hf3 : f 3=0 := by
    simp [f, fineFieldGeometryEnvelope_count_three]
  rw [finite_refined_sum_eq_start_four D hD f hf3]
  have hmajor : ∑ j ∈ Finset.range 𝔐, f 𝔍 ≤
      ∑ j ∈ Finset.range 𝔐, poissonCountWeight 𝔓 𝔍 *
        finePairEvenActionSpatialBudget d 𝔍 M q ad bd C a rho eta ell := by
    apply Finset.sum_le_sum
    intro j _
    have h := mul_le_mul_of_nonneg_left
      (fineFieldGeometryEnvelope_integrable_and_le (d := d) (n := 𝔍)  𝖡₃ 
        ad bd ell N hell M q C a rho eta).2
      $ poissonCountWeight_nonneg (by positivity : 𝔙 𝔉) 𝔍
    convert h using 1
    try dsimp
    rw [← mul_assoc, poissonCountWeight_mul_pow]
    ring
  exact hmajor.trans $ finite_fine_pair_field_budget_le haD had hbd hab htau d M q 𝔐
    C a rho eta ell 𝔅 mu  𝖠₃  hmu hmu1

𝗇 𝔏 𝔚 finePairAliasGeometryEnvelope
𝗇 𝔒 ∑ j ∈ 𝔈, poissonCountWeight 𝔉 𝔄 * if M<𝔄 then ∫ U, 𝔏 ∂fullSpatialPatchDesign d 𝔄 else 0
𝗇 𝔔 𝔜 finePairSaddleAliasFactorialConstant K 𝔅
theorem finite_fine_pair_alias_geometry_budget_le {d D : ℕ} [NeZero d] (hd : 𝘚)
    {aD bD ad bd c0 K : ℝ} (haD : 𝘗₂) (had : aD ≤ ad) (hbd : bd ≤ bD)
    (hab : 𝖽) (htau : 𝔊 ≤ c0)
    (hc0 : 𝔙 c0) (hK : 𝔙 K) (M q : ℕ) C a rho eta ell N Cs mu
    (hN : 𝘹) (hell : ell=𝗐) (hell1 : 𝗲₁)
    (hellN : ell ≤ N) (hDM : 𝚋₁)
    (hCs : 𝔙 Cs) (hmu : 𝔙 mu) (hmu1 : 𝗦₁) :
    𝔒 ≤
      𝔔 *
        (𝗸*N^(4-𝔖)) *
          poissonCountWeight (𝔔*mu) 𝖦₁ := by
  let f := fun r => poissonCountWeight 𝔓 r *
    finePairAliasActionSpatialBudget d r M q ad bd C a rho eta ell
  have hf r : 0 ≤ f r := by
    dsimp [f, finePairAliasActionSpatialBudget]
    have h := poissonCountWeight_nonneg (by positivity : 𝔙 𝔓) r
    have hK := spatialInverseFourConstant_nonneg d
    positivity
  have hmajor : 𝔒 ≤
      ∑ j ∈ 𝔈, if M<𝔄 then f 𝔄 else 0 := by
    apply Finset.sum_le_sum
    intro j _
    by_cases hMj : M<𝔄
    · simp only [if_pos hMj]
      have h := mul_le_mul_of_nonneg_left
        (finePairAliasGeometryEnvelope_integrable_and_le (d := d) (n := 𝔄)  𝖡₃ 
          ad bd ell N (lt_of_lt_of_le zero_lt_one hell1) hellN M q C a rho eta).2
        $ poissonCountWeight_nonneg (by positivity : 𝔙 𝔉) 𝔄
      convert h using 1
      dsimp [f]
      rw [← mul_assoc, poissonCountWeight_mul_pow]
      ring
    bound
  apply (hmajor.trans $ finite_refined_gated_sum_le_tail D M f hf ).trans
  exact finite_fine_pair_saddle_alias_budget_le  𝖡₃  haD had hbd hab htau hc0 hK M D q 𝘀₂
    C a rho eta ell N 𝔅 mu hN hell hDM  𝖠₃  hmu hmu1
