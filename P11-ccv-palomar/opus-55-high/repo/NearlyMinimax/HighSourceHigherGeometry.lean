module

public import NearlyMinimax.HighSpatialEnvelopes
public import NearlyMinimax.HigherBandRawCollapse
public import NearlyMinimax.HighSourceHigherCounts
public import NearlyMinimax.OrdinaryFineAliasGeometryEnvelope
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Actual full higher-count source numerator and a deterministic geometric
square envelope. All signed rows are summed before the one heat correction. -/
𝚫
𝚨
𝚩
𝚭
𝚬

 set_option hygiene false
𝗇 𝔛 𝙬
𝗇 𝔅 fun v => 𝖨 𝔛 v y
𝗃 𝔢 ἀ ad bd
𝗇 𝔣 𝗊
𝗇 𝔥 ∀ i, p i ∈ 𝔢 Icc
𝗇 𝔦 𝖠₁
𝗃 𝔭 1 ≤ ἀ
theorem highCardinalRawNumerator_eq_matrix_heat {d n F }
    ad bd lam (haD : 𝖼) (hab : 𝖽) (hlam : 𝖺)
    {T } (hT : 𝔭 T) m D q (hn : 𝔭 n) (hnm : n ≤ m)
    (hnD : 𝔦) (hnF : n ≤ F) C a V η (hC : 𝚆)
    U (hU : ∀ i l, |𝚅| ≤ 2)
    (p g w : 𝙔) (hp : 𝔥)
    (c : 𝖲) y :
    𝔢 highCardinalRawNumerator lam T m D q C a V η U p g w c y =
      𝔣*𝗔 𝖯₁ c
        𝔅 -
      𝙎*𝔣*∑ i, 𝖩*𝖷 𝔛 c y i := by
  rw [𝔢 highCardinalRawNumerator_eq_alias_defect lam haD hab hlam hT m D q hn hnm hnD hnF
    C a V η hC U hU p g w hp c y, 𝙿₂]
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
  ring

 set_option hygiene false
𝗇 𝔜 Fin 𝘐
𝗇 𝔞 𝙳
𝗃 𝔫 higherBandTargetScale d ἀ N μ
𝗇 𝔊 ∀ j : 𝔜, 0 < 𝔫 𝔞
𝗇 𝔚 𝔫 n
theorem higherBandTargetScale_pos_of_physical {d n D } (hn : 𝖬₂) (hnD : 𝔦)
    N μ (hnu : 𝔊) :
    0 < 𝔚 := by
  let j : 𝔜 := ⟨n-3, 𝖡₃⟩
  have hj : 𝔞 = n := 𝖤₃
  simpa only [hj] using hnu j

 set_option hygiene false
𝗇 𝔇 max 1 𝔚
𝗇 𝔈 fun r => 𝔫 r
𝗇 𝔉 ordinaryFineAliasTargetSet d D ℓ N μ
𝗇 𝔍 ∀ j : 𝔜, ℓ < 𝔫 𝔞 → 𝔞 ≤ M
𝗇 𝔎 M<n
𝗃 𝔩 𝔢 ἀ ℓ N
𝗃 𝔱 𝔩 ἀ M q C U p c 𝔅
𝗇 𝔗 if 𝔎 then 𝔱 finePairPairAliasAction else 0
𝗇 𝔘 𝔱 finePairEvenFieldAction
𝗃 𝔮 𝔢 ἀ lam ℓ N μ
theorem completeSourceRawNumerator_higher_components {d n : ℕ} [NeZero d]
    ad bd lam ℓ N μ (haD : 𝖼) (hab : 𝖽) (hlam : 𝖺) (hℓ : 𝔭 ℓ)
    D M q (hn : 𝖬₂) (hnD : 𝔦)
    (hnu : 𝔊)
    (hFine : 𝔍)
    C a V η (hC : 𝚆) U (hU : ∀ i l, |𝚅| ≤ 2)
    (p g w : 𝙔) (hp : 𝔥) (c : 𝙮 → ℝ) y :
    𝔮 completeSourceRawNumerator D M q C a V η U p g w c y =
      𝔢 highCardinalRawNumerator lam 𝔇 D D q C a V η U p g w c y +
      (if 𝔎 then ordinaryFineAliasFamilyRawAction 𝔉
        ad bd lam ℓ 𝔈 M q C a V η U p g w c y else 0) +
      𝔗 +
      𝔘 := by
  have hmat : integratedCardinalMatrix (D := D) lam 𝔇 U =
      integratedCardinalMatrix lam 𝔚 U := by
    funext γ δ
    exact integrated_cardinal_matrix_max_one  𝖡₃  lam (higherBandTargetScale_pos_of_physical hn hnD N μ hnu) U γ δ
  rw [𝔮 completeSourceRawNumerator_higher haD hab D M q hn hnD C a V η U p g w hp c y,
    𝔮 higherBandFamilyFirstAction_matched_and_full_fine_alias haD hab hlam hℓ D M q hn hnD hnu hFine
      C a V η U hU p g w hp c y,
    𝔢 highCardinalRawNumerator_eq_matrix_heat lam haD hab hlam (le_max_left ..) D D q  𝖡₃  hnD hnD hnD
      C a V η hC U hU p g w hp c y, hmat]
  by_cases hnM : 𝔎
  · bound
  · rw [if_neg hnM, 𝔩 finePairPairAliasAction_zero_selected_count haD hab M q hn (le_of_not_gt hnM) C U p c]
    bound

 set_option hygiene false
𝗇 𝔄 𝖧⁻¹
𝗇 𝔓 bD-𝔄
𝗇 𝔔 aD+𝔄
𝗃 𝔨 ἀ (F := D)
𝗃 𝔡 𝔨 ἀ 𝔉 M R q aD bD c0 C a ρ η ℓ 𝔈 U
𝗇 𝔖 if 𝔎 then 𝔡 ordinaryFineAliasFamilyResponseSquareEnvelope else 0
𝗃 𝔟 ἀ 𝔔 𝔓 ℓ N M q C a ρ η U
𝗇 𝔤 𝙇
𝗃 𝔯 𝔨 ἀ q 𝔓 C a ρ η 𝔇 U
def completeSourceHigherGeometryEnvelope {d n D : ℕ} (aD bD c0 ℓ N μ : ℝ)
    (M R q : ℕ) (C a ρ η : ℝ) (U : 𝔤) : ℝ :=
  4*(𝔯 cardinalGeometryEnvelope +
    𝔖 +
    (if 𝔎 then 𝔟 finePairAliasGeometryEnvelope else 0) +
    𝔟 fineFieldGeometryEnvelope)

 set_option hygiene false
𝗇 𝔙 completeSourceHigherGeometryEnvelope (D := D) aD bD c0 ℓ N μ M R q C a ρ η
𝗇 𝔏 𝔙 U
theorem completeSourceHigherGeometryEnvelope_nonneg {d n D } aD bD c0 ℓ N μ
    M R q C a ρ η (U : 𝔤) :
    0 ≤ 𝔏 := by
  unfold completeSourceHigherGeometryEnvelope
  have hA := 𝔯 cardinalGeometryEnvelope_nonneg
  have hB := 𝔡 ordinaryFineAliasFamilyResponseSquareEnvelope_nonneg
  have hP := 𝔟 finePairAliasGeometryEnvelope_nonneg
  have hF := 𝔟 fineFieldGeometryEnvelope_nonneg
  positivity

 set_option hygiene false
𝗃 𝔠 fun _ => ἀ
𝗃 𝔪 ἀ y^2
𝗃 𝔲 ∑ y, 𝔪 ἀ
theorem completeSourceRawNumerator_higher_square_le_geometry {d n : ℕ} [NeZero d]
    (aD bD c0 ℓ N μ : ℝ) (haD : 𝘗₂) (hℓ : 𝔭 ℓ) (D M R q : ℕ)
    (hshrink : 𝔔 < 𝔓) (htau : shrunkDensityExponent aD bD M ≤ c0)
    (hn : 𝖬₂) (hnD : 𝔦) (hq : 𝔭 q)
    (hnu : 𝔊)
    (hFine : 𝔍)
    (hI : ∀ r ∈ 𝔉, 𝔭 r ∧ r ≤ R)
    (C a V η ρ : ℝ) (hC : 𝔭 C) (ha : 𝙆) (hη : 𝗼) (hρ : 𝗛₁) (hηρ : η ≤ 𝙸)
    U (hU : ∀ i l, |𝚅| ≤ 2)
    p g w (hpD : ∀ i, p i ∈ Icc 𝔔 𝔓)
    (hg : ∀ i, |g i| ≤ 𝙸) (hw : ∀ i, |w i| ≤ 1) (c : 𝙮 → ℝ)
    (hc : ∑ γ, |c γ| ≤ 𝗳) (hp : ∀ f : ℝ, |f| ≤ ρ → 𝘃) :
     ∑ y : 𝙈, completeSourceRawNumerator 𝔔 𝔓
      (spatialInterpolationLambda d) ℓ N μ D M q C a V η U p g w c y^2 ≤
      𝔏 := by
  let ad := 𝔔
  let bd := 𝔓
  have had : 𝖼 := 𝖠₃
  let A := fun y => 𝔢 highCardinalRawNumerator (spatialInterpolationLambda d)
    𝔇 D D q C a V η U p g w c y
  let B := fun y => if 𝔎 then ordinaryFineAliasFamilyRawAction 𝔉
    ad bd (spatialInterpolationLambda d) ℓ 𝔈 M q C a V η U p g w c y else 0
  let P := fun y => 𝔗
  let F := fun y => 𝔘
  have hA := highCardinalRawNumerator_sum_square_le_geometry (T := 𝔇) ad bd had hshrink 𝚂₁ D D q
     𝖡₃  hnD hnD hnD hq C a V η ρ hC ha hη hρ hηρ U hU p g w hpD hg hw c hc hp
  have hB : 𝔲 B ≤ 𝔖 := by
    by_cases hMn : 𝔎
    · simp only [B, if_pos hMn]
      exact ordinaryFineAliasFamilyResponseSquareEnvelope_dominates _ aD bD c0 ℓ _ haD hshrink htau hI q
         𝖡₃  C a V η ρ hC ha hη hρ hηρ U hU 𝔠 p 𝔠 g 𝔠 w 𝔠 c
          𝔠 hpD 𝔠 hg 𝔠 hw 𝔠 hc hp
    · simp [B, hMn]
  have hP : 𝔲 P ≤ if 𝔎 then 𝔩 finePairAliasGeometryEnvelope M q C a ρ η U else 0 := by
    by_cases hMn : 𝔎
    · simp only [P, if_pos hMn]
      exact 𝔩 finePairPairAliasAction_sum_square_le_geometry had hshrink M q  𝖡₃  C a V η ρ
        hC ha hη hρ hηρ U hU p g w hpD c hc hg hw hp
    grind
  have hF := 𝔩 finePairEvenFieldAction_sum_square_le_geometry had hshrink M q  𝖡₃  C a V η ρ
    hC ha hη hρ hηρ U hU p g w hpD c hc hg hw hp
  have hb (y : 𝙈) : 𝔢 completeSourceRawNumerator (spatialInterpolationLambda d) ℓ N μ
      D M q C a V η U p g w c y^2 ≤ 4*(𝔪 A+𝔪 B+𝔪 P+𝔪 F) := by
    rw [𝔢 completeSourceRawNumerator_higher_components _ ℓ N μ had hshrink (by unfold spatialInterpolationLambda; positivity) hℓ D M q hn hnD
      hnu hFine C a V η (lt_of_lt_of_le zero_lt_one hC).ne' U hU p g w hpD c y]
    nlinarith only [sq_nonneg $ A y-B y , sq_nonneg $ P y-F y , sq_nonneg $ A y+B y-P y-F y ]
  have h := 𝗣₁ fun y _ => hb y
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  exact h.trans $ by
    unfold completeSourceHigherGeometryEnvelope
    linarith

 set_option hygiene false
𝗇 𝔐 𝖮₁
𝗇 𝔑 ordinaryFineAliasAmplitudeFactor n M R q ad bd c0 C a ρ η
𝗇 𝔒 hL.trans (hI r hr).2
theorem ordinaryFineAliasFamilyResponseSquareEnvelope_integrable {d n F }
    (hd : 𝘚) I M R q ad bd c0 C a ρ η L
    T (hL : 𝔭 L) (hI : ∀ r ∈ I, 𝘠₁ ∧ L ≤ T r) :
    Integrable (ordinaryFineAliasFamilyResponseSquareEnvelope (F := F)
      I M R q ad bd c0 C a ρ η L T) 𝔐 := by
  let f := fun r (U : 𝔤) => 𝔑 *
    ordinaryFineAliasGeometryKernel (F := F) r L (T r) U
  have hm r hr : Measurable $ f r :=
    (ordinaryFineAliasGeometryKernel_measurable r hL 𝔒).const_mul _
  have hi r (hr : r ∈ I) : Integrable (fun U => f r U^2) 𝔐 := by
    have h := (ordinaryFineAliasKernel_sum_square_integrable_and_le (F := F) (n := n)
      hd (hI r hr).1 hL 𝔒 (hI r hr).2).1.const_mul
        $ 𝔑^2
    convert h using 1
    funext U
    dsimp [f, ordinaryFineAliasGeometryKernel]
    ring
  have hs : Integrable (fun U => (∑ r ∈ I, f r U)^2) 𝔐 := by
    have h := finite_sum_abs_square_integrable 𝔐 I f hm hi
    apply h.mono' ((Finset.measurable_sum I hm).pow_const 2).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro U
    simpa only [Real.norm_eq_abs, abs_sq, sq_abs] using
      (𝘉 $ Finset.sum_nonneg 𝖢 ).mpr $ Finset.abs_sum_le_sum_abs (fun r => f r U) I
  exact hs.const_mul $ 3^n

 𝗇 𝔧 lt_of_lt_of_le zero_lt_one hℓ
𝗃 𝔬 ἀ (d := d) (n := n)
theorem completeSourceHigherGeometryEnvelope_integrable {d n D : ℕ} [NeZero d]
    (hd : 𝘚) (hn : 𝗏) aD bD c0 ℓ N μ M R q C a ρ η
    (hℓ : 𝔭 ℓ) (hN : ℓ ≤ N) :
    Integrable 𝔙 𝔐 := by
  have hA := (𝔨 cardinalGeometryEnvelope_integrable_and_le hd hn q 𝔓 C a ρ η
    (T := 𝔇) $ le_max_left .. ).1
  have hB := ordinaryFineAliasFamilyResponseSquareEnvelope_integrable (n := n) (F := D) hd
    𝔉 M R q aD bD c0 C a ρ η ℓ
    𝔈 hℓ fun r hr => by
      have h := (Finset.mem_filter.mp hr).2
      bound
  have hP := (𝔬 finePairAliasGeometryEnvelope_integrable_and_le  𝖡₃ 
    𝔔 𝔓 ℓ N 𝔧 hN M q C a ρ η).1
  have hF := (𝔬 fineFieldGeometryEnvelope_integrable_and_le  𝖡₃ 
    𝔔 𝔓 ℓ N 𝔧 M q C a ρ η).1
  unfold completeSourceHigherGeometryEnvelope
  split_ifs
  all_goals fun_prop
