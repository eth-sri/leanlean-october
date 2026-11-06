module

public import NearlyMinimax.HighCardinalSpatialEnergy
public import NearlyMinimax.FinePairCountTwoSpatialEnergy
public import NearlyMinimax.HighSelectedScoreEnergy
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Universal deterministic spatial envelopes for the actual signed
response numerators. These depend only on the local chart and fixed caps. -/
𝚫
𝚨
𝚩
𝚭
𝚬

 set_option hygiene false
𝗇 𝔑 𝙇
𝗇 𝔖 cardinalWeightDefect i (spatialInterpolationLambda d) T U
𝗇 𝔚 𝘔₁
𝗇 𝔩 𝗶₂
𝗇 𝔱 (3 : ℝ)^n
def cardinalGeometryEnvelope {d n F : ℕ} (q : ℕ) (bd C a ρ η T : ℝ)
    (U : 𝔑) : ℝ :=
  𝔱 * (𝔩 *
    (∑ i, 𝔖)^2 +
    𝔚 *
      spatialMatrixL1 (integratedCardinalMatrix (D := F) (spatialInterpolationLambda d) T U)^2)

 set_option hygiene false
𝗇 𝔢 cardinalGeometryEnvelope (F := F) q bd C a ρ η T
𝗇 𝔍 𝔢 U
𝗃 𝔴 0 ≤ ἀ
theorem cardinalGeometryEnvelope_nonneg {d n F } q bd C a ρ η T
    (U : 𝔑) : 𝔴 𝔍 := by
  unfold cardinalGeometryEnvelope
  positivity

 set_option hygiene false
𝗇 𝔉 𝖮₁
𝗃 𝔳 ∫ U, ἀ ∂ 𝔉
𝗃 𝔵 ἀ (D := F) hd hn hT
𝗃 𝔶 1 ≤ ἀ
theorem cardinalGeometryEnvelope_integrable_and_le {d n F } (hd : 𝘚) (hn : 𝗏)
    q bd C a ρ η {T } (hT : 𝔶 T) :
    Integrable 𝔢
      𝔉 ∧
    𝔳 𝔍 ≤
       3 ^n * cardinalRawSpatialEnergyBudget d n q bd C a ρ η T := by
  have hlam : 𝘹₂ := by unfold spatialInterpolationLambda; positivity
  have hZ : Integrable (fun U => (∑ i : Fin n, 𝔖)^2)
      𝔉 := by
    have h := finite_sum_abs_square_integrable 𝔉 Finset.univ
      (fun i U => 𝔖)
      (fun i _ => cardinalWeightDefect_measurable i _ hT)
       fun i _ => cardinalWeightDefect_square_integrable i hlam hT
    simpa only [abs_of_nonneg (cardinalWeightDefect_mem_unit _ hlam T _).1] using h
  have hE := 𝔵 integratedCardinalMatrix_full_square_integrable
  refine ⟨ ((hZ.const_mul _).add $ hE.const_mul _ ).const_mul _ , ?_⟩
  unfold cardinalGeometryEnvelope
  rw [integral_const_mul, integral_add (hZ.const_mul _) $ hE.const_mul _ , integral_const_mul, integral_const_mul]
  have h := add_le_add (mul_le_mul_of_nonneg_left (cardinalWeightDefect_sum_square_integral_le (d := d)  𝖡₃  hn hT)
    (by positivity : 𝔴 𝔩))
    $ mul_le_mul_of_nonneg_left 𝔵 integratedCardinalMatrix_full_square_integral_le
      (by positivity : 𝔴 𝔚)
  simpa

 set_option hygiene false
𝗇 𝔎 𝖳
𝗇 𝔘 𝖲
𝗇 𝔜 𝙸
𝗇 𝔪 𝙈
𝗇 𝔫 𝖼
𝗇 𝔬 𝖽
𝗇 𝔭 𝙆
𝗇 𝔮 𝔴 ρ
theorem highCardinalRawNumerator_sum_square_le_geometry {d n F }
    ad bd (haD : 𝔫) (hab : 𝔬) {T } (hT : 𝔶 T)
    m D q (hn : 𝔶 n) (hnm : n ≤ m) (hnD : 𝖠₁) (hnF : n ≤ F) (hq : 𝔶 q)
    C a V η ρ (hC : 𝔶 C) (ha : 𝔭) (hη : 𝔴 η) (hρ : 𝔮)
    (hηρ : η ≤ 𝔜) U (hU : ∀ i l, |𝚅| ≤ 2)
    p g w (hpD : 𝔎)
    (hg : ∀ i, |g i| ≤ 𝔜) (hw : ∀ i, |w i| ≤ 1)
    (c : 𝔘) (hc : ∑ γ, |c γ| ≤ 𝗳)
    (hp : ∀ f , |f| ≤ ρ → 𝘃) :
     ∑ y : 𝔪, highCardinalRawNumerator ad bd (spatialInterpolationLambda d) T m D q
      C a V η U p g w c y^2 ≤ 𝔍 := by
  have hlam : 𝘹₂ := by unfold spatialInterpolationLambda; positivity
  have h := 𝗣₁ fun y _ =>
    highCardinalRawNumerator_square_bound_of_chart ad bd _ haD hab hlam hT m D q hn hnm hnD hnF hq
      C a V η ρ hC ha hη hρ hηρ U hU p g w hpD hg hw c hc hp y
  exact h.trans_eq $ by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow]; rfl

 set_option hygiene false
𝗇 𝔅 ((Finset.univ : 𝙍).powerset).filter fun S => 4 ≤ S.card ∧ Even S.card
𝗃 𝔷 ἀ^2
𝗇 𝔈 𝔱 * (𝗺₁ * (𝘁*𝙒^2*𝔷 η))^2
𝗇 𝔊 finePairTimeSubsetMoment T0 N U S
def fineFieldGeometryEnvelope {d n : ℕ} (ad bd T0 N : ℝ) (M q : ℕ) (C a ρ η : ℝ)
    (U : 𝔑) : ℝ :=
  𝔈 *
      (∑ S ∈ 𝔅,
        |𝔊|)^2

 set_option hygiene false
𝗇 𝔒 (Finset.univ : 𝙍).powersetCard 2
def finePairAliasGeometryEnvelope {d n : ℕ} (ad bd T0 N : ℝ) (M q : ℕ) (C a ρ η : ℝ)
    (U : 𝔑) : ℝ :=
  𝔈 *
      (∑ S ∈ 𝔒, |𝔊|)^2

 set_option hygiene false
𝗃 𝔧 ἀ ad bd T0 N M q C
𝗇 𝔣 𝔧 fineFieldGeometryEnvelope a ρ η
𝗇 𝔏 𝔣 U
theorem fineFieldGeometryEnvelope_nonneg {d n } ad bd T0 N M q C a ρ η
    (U : 𝔑) : 𝔴 𝔏 := by
  unfold fineFieldGeometryEnvelope; positivity

 set_option hygiene false
𝗇 𝔤 𝔧 finePairAliasGeometryEnvelope a ρ η
𝗇 𝔐 𝔤 U
theorem finePairAliasGeometryEnvelope_nonneg {d n } ad bd T0 N M q C a ρ η
    (U : 𝔑) : 𝔴 𝔐 := by
  unfold finePairAliasGeometryEnvelope; positivity

 set_option hygiene false
𝗇 𝔇 𝗺₁ * (𝘁*𝔷 n*𝔷 η)
𝗇 𝔛 fun S _ => finePairTimeSubsetMoment_measurable T0 N S
𝗇 𝔡 finite_sum_abs_square_integrable 𝔉 s (fun S U => 𝔊) 𝔛
𝗃 𝔨 3 ^n*ἀ d n M q ad bd C a ρ η T0
𝗇 𝔲 hs S hS
theorem fineFieldGeometryEnvelope_integrable_and_le {d n : ℕ} [NeZero d] (hd : 3 ≤ d)
    ad bd T0 N (hT0 : 0 < T0) M q C a ρ η :
    Integrable 𝔣 𝔉 ∧
    𝔳 𝔏 ≤
      𝔨 finePairEvenActionSpatialBudget := by
  let s := 𝔅
  have hs S (hS : S ∈ s) := (Finset.mem_filter.mp hS).2.1
  have hi := 𝔡
     fun S hS => finePairTimeSubsetMoment_square_integrable hd hT0 S 𝔲
  refine ⟨hi.const_mul _, ?_⟩
  unfold fineFieldGeometryEnvelope
  rw [integral_const_mul]
  have h := mul_le_mul_of_nonneg_left (finePairTimeSubsetMoment_sum_abs_square_integral_le hd (hi := N) hT0 s hs)
    (by positivity : 0 ≤ 3^n*𝔷 𝔇)
  exact h.trans_eq $ by unfold finePairEvenActionSpatialBudget; ring

 set_option hygiene false
𝗇 𝔓 finePairTimeSubsetMoment_two_subset_square_integrable_and_le hd hT0 hN S 𝔲
theorem finePairAliasGeometryEnvelope_integrable_and_le {d n : ℕ} [NeZero d] (hd : 4 < d)
    ad bd T0 N (hT0 : 0 < T0) (hN : 𝖽₂) M q C a ρ η :
    Integrable 𝔤 𝔉 ∧
    𝔳 𝔐 ≤
      𝔨 finePairAliasActionSpatialBudget := by
  let s := 𝔒
  have hs S (hS : S ∈ s) := (Finset.mem_powersetCard.mp hS).2
  have hi := 𝔡
     fun S hS => (𝔓).1
  refine ⟨hi.const_mul _, ?_⟩
  unfold finePairAliasGeometryEnvelope
  rw [integral_const_mul]
  have h := finite_sum_square_integral_le 𝔉 s
    (fun S U => |𝔊|)
    (2^(d*𝗥)*(6*𝗝*spatialInverseFourConstant d/T0^𝗗₁))
    (fun S _ => (finePairTimeSubsetMoment_measurable T0 N S).abs)
     fun S hS => by simpa only [sq_abs] using (𝔓).1
     fun S hS => by simpa only [sq_abs] using (𝔓).2
  exact (mul_le_mul_of_nonneg_left h 𝖠₃ ).trans_eq $ by
      rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
      unfold finePairAliasActionSpatialBudget
      ring

𝗇 𝔥 𝙬
𝗇 𝔄 fun v => 𝖨 𝔥 v y
𝗇 𝔔 (𝘉 $ (abs_nonneg _).trans h ).mpr h
𝗇 𝔗 𝗣₁ 𝘖₂
𝗇 𝔞 𝘀
𝗇 𝔟 𝔧 finePairPairAliasAction U p c 𝔄^2
𝗃 𝔦 ἀ ad bd T0 N haD hab M q hn C a V η ρ hC ha hη hρ hηρ U hU p g w hpD c y hc hg hw hp
𝗇 𝔯 𝔷 K*𝔷 Z
𝗃 𝕬 ∑ y : 𝔪, ἀ
theorem finePairPairAliasAction_sum_square_le_geometry
    ad bd T0 N (haD : 𝔫) (hab : 𝔬) M q (hn : 𝔶 n)
    C a V η ρ (hC : 𝔶 C) (ha : 𝔭) (hη : 𝔴 η) (hρ : 𝔮)
    (hηρ : η ≤ 𝔜) U (hU : ∀ i l, |𝚅| ≤ 2)
    p g w (hpD : 𝔎)
    (c : 𝔘)
    (hc : ∑ γ, |c γ| ≤ 𝗳) (hg : ∀ i, |g i| ≤ 𝔜) (hw : ∀ i, |w i| ≤ 1)
    (hp : ∀ f , |f| ≤ ρ → 𝔞) :
    𝕬 𝔟 ≤
        𝔐 := by
  let K := 𝔇
  let s := 𝔒
  let Z := ∑ S ∈ s, |𝔊|
  have hy y : 𝔟 ≤ 𝔯 := by
    have h := 𝔦 finePairPairAliasAction_abs_bound_of_chart
    have he : (∑ S ∈ Finset.univ.powerset,
        if S.card = 2 then |𝔊| else 0) = Z := by
      dsimp [Z, s]
      rw [Finset.powersetCard_eq_filter, Finset.sum_filter]
    rw [he] at h
    change |_| ≤ K*Z at h
    simpa only [sq_abs, mul_pow] using 𝔔
  have h := 𝔗
  exact h.trans_eq $ by
    simp
    unfold finePairAliasGeometryEnvelope
    ring

𝗇 𝔠 𝔧 finePairEvenFieldAction U p c 𝔄^2
theorem finePairEvenFieldAction_sum_square_le_geometry
    ad bd T0 N (haD : 𝔫) (hab : 𝔬) M q (hn : 𝔶 n)
    C a V η ρ (hC : 𝔶 C) (ha : 𝔭) (hη : 𝔴 η) (hρ : 𝔮)
    (hηρ : η ≤ 𝔜) U (hU : ∀ i l, |𝚅| ≤ 2)
    p g w (hpD : 𝔎)
    (c : 𝔘)
    (hc : ∑ γ, |c γ| ≤ 𝗳) (hg : ∀ i, |g i| ≤ 𝔜) (hw : ∀ i, |w i| ≤ 1)
    (hp : ∀ f , |f| ≤ ρ → 𝔞) :
    𝕬 𝔠 ≤
        𝔏 := by
  let K := 𝔇
  let s := 𝔅
  let Z := ∑ S ∈ s, |𝔊|
  have hy y : 𝔠 ≤ 𝔯 := by
    have h := 𝔦 finePairEvenFieldAction_abs_bound_of_chart
    have he : (∑ S ∈ Finset.univ.powerset,
        if 4 ≤ S.card ∧ Even S.card then |𝔊| else 0) = Z := by
      dsimp [Z]
      rw [Finset.sum_filter]
    rw [he] at h
    change |_| ≤ K*Z at h
    simpa only [sq_abs, mul_pow] using 𝔔
  have h := 𝔗
  exact h.trans_eq $ by
    simp
    unfold fineFieldGeometryEnvelope
    ring

 def finePairCountTwoGeometryEnvelope {d : ℕ} (bd a ρ η N : ℝ) (U : 𝖿₁) : ℝ :=
  9*(𝔷 η*𝔷 bd*(𝗠/𝔷 a)^2)^2*finePairDistanceFactor N (U 0) (U 1)^2

 set_option hygiene false
𝗇 𝔰 finePairCountTwoGeometryEnvelope bd a ρ η N
𝗇 𝔙 𝔰 U
theorem finePairCountTwoGeometryEnvelope_nonneg {d } bd a ρ η N
    (U : 𝖿₁) : 𝔴 𝔙 := by
  unfold finePairCountTwoGeometryEnvelope; positivity

 theorem finePairCountTwoGeometryEnvelope_integrable_and_le {d } (hd : 𝗆)
    bd a ρ η {N } (hN : 𝘹) :
    Integrable 𝔰 𝗿₂ ∧
     ∫ U, 𝔙 ∂𝗿₂ ≤
      9*finePairCountTwoSpatialBudget d bd a ρ η N := by
  have hp := measurePreserving_finTwoArrow 𝖪
  have hi := hp.integrable_comp_of_integrable $ finePairDistanceFactor_square_integrable hN
  refine ⟨hi.const_mul _, ?_⟩
  unfold finePairCountTwoGeometryEnvelope
  rw [integral_const_mul]
  have hInt :=
    (hp.integral_comp MeasurableEquiv.finTwoArrow.measurableEmbedding _).trans_le
      $ finePairDistanceFactor_square_integral_le hd hN
  exact (mul_le_mul_of_nonneg_left hInt 𝖠₃ ).trans_eq
    $ by unfold finePairCountTwoSpatialBudget; ring
theorem finePairCountTwoRawNumerator_sum_square_le_geometry [NeZero d] (hF : 3 ≤ F)
    ad bd T0 N (haD : 𝔫) (hab : 𝔬) (hT0 : 𝔴 T0) (hN : 𝖽₂)
    D M q (hD : 2 ≤ D) (hM : 𝗜₁) (hq : 𝖯₂)
    C a V η ρ (hC : 𝚆) (ha : 𝔭) (hρ : 𝔮)
    U (hU : 𝖾₁)
    p g w (hp : 𝔎) (hw : ∀ i, |w i| ≤ 1)
    (c : 𝔘)
    (hf : ∀ i, |𝗡 𝔥 c i| ≤ ρ) :
     ∑ y : Fin 2 → Fin 3, 𝙬₂^2 ≤
      𝔙 :=
    finePairCountTwoRawNumerator_sum_square_le hF ad bd T0 N haD hab hT0 hN D M q hD hM hq
      C a V η ρ hC ha hρ U hU p g w hp hw c hf
