module

public import NearlyMinimax.HighSourceOriginalGeometry
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Uniform, actual canonical-source domination by the full-count geometry
H. No hypothesis asserts score boundedness or a stochastic covariance. -/
𝚫
𝚪
𝚨
𝚩
set_option maxHeartbeats 1800000
𝚬
𝚿

 set_option hygiene false
𝗇 𝔎 n+3
𝗃 𝔚 selectedRawSquareEnergy (highUnionSourceRawNumerator C R ἀ Q.a V eta h j) x
𝗇 𝔄 𝔚 𝔎 ≤ if 𝔎 ≤ D then completeSourceHigherGeometryEnvelope C.densityLower C.densityUpper c0 ell N mu M Rbound q Cfr Q.a Q.ρ eta U else 𝚎₁^𝔎*𝗸*(highRowTotalMass R.rowMass+1)^2
𝗇 𝔏 𝖧
𝗇 𝔅 finePairCountTwoRawNumerator (C.densityLower+1/𝔏) (C.densityUpper-1/𝔏) ell N D M q Cfr Q.a V eta U p g w (c j) y
𝗇 𝔇 le_max_right _ _
𝗇 𝔈 (min_le_right _ _).trans
𝗇 𝔉 min_le_left _ _
𝗇 𝔊 𝚂₁
𝗇 𝔙 highUnionSourceRawNumerator C R 2 Q.a V eta h j
𝗇 𝔍 selectedRawSquareEnergy 𝔙 x
𝗃 𝔐 ἀ k D M q hk0 horder hk hD
𝗇 𝔑 higherBandTargetScale d 𝙳 N mu
𝗇 𝔒 𝖿
𝗇 𝔓 𝘐
𝗃 𝔜 ἀ d k
𝗇 𝔔 𝔜 highPatchProductChart j x
𝗃 𝔞 (ἀ).trans
𝗇 𝔖 𝔞 𝔊
𝗇 𝔗 min_le_right _ _
𝗇 𝔘 𝖻
𝗃 𝔛 ἀ hD _ _ ell N had hab hellp.le hellN.le D M q
𝗃 𝔟 ἀ Q.a Q.ρ C.densityUpper 1 1
theorem completeSource_original_all_geometry {d : ℕ} [NeZero d]
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) :
    ∃ Cfr0 eta0 : ℝ, 𝚣₂ ∧ 𝖴₁ ∧
      ∀ k D M q : ℕ, ∀ (_ : NeZero k), ∀ (_ : LinearOrder 𝔜 HighWindowLabels),
      𝗑 → 𝗕 → 𝖯₂ → highCenterResolutionThreshold C ≤ 𝔏 →
      ∀ Cfr c0 ell N mu cf : ℝ, Cfr0 ≤ Cfr → 𝗲₁ → 𝘈₂ → 𝚐₁ →
      cf*𝙦^(-C.smoothness) ≤ eta0 →
      𝙲 M ≤ c0 →
      (∀ j : Fin 𝔓, 0 < 𝔑) →
      (∀ j : Fin 𝔓, ell < 𝔑 → 𝙳 ≤ M) →
      ∀ Rbound : ℕ, (∀ r ∈ 𝗊₁, 𝘗 ∧ r ≤ Rbound) →
      ∀ V : ℝ, |𝖮₂| ≤ Q.ρ → ∀ j : 𝔜 HighWindowLabels,
      ∀ h ,
      ∀ n : ℕ, ∀ x : 𝙇, (∀ i, x i ∈ 𝔜 highTorusPatch j) →
      let R := 𝔘 (spatialInterpolationLambda d) ell N mu
      let eta := 𝔒
      let Chi := 𝔟 highSeparatedScoreExponentialConstant
      𝔚 n ≤
        𝙱₂ (highRowTotalMass R.rowMass) n 𝔔 := by
  obtain ⟨CG,eG,hCG,heG,hguards⟩ := completeSource_original_local_guards C Q
  obtain ⟨CR,eR,hCR,heR,hresponse⟩ := completeSource_original_response_exact_and_low_counts C Q
  obtain ⟨CP,eP,hCP,heP,hpair⟩ := completeSource_original_count_two C Q
  obtain ⟨CH,eH,hCH,heH,hhigher⟩ := completeSource_original_higher_geometry C Q
  obtain ⟨CB,eB,hCB,heB,hcrude⟩ := completeSourceNumerator_original_field_bound C Q
  let C0 := max (max CG CR) $ max CP $ max CH CB
  let e0 := min (min eG eR) $ min eP $ min eH eB
  have hG0 : CG ≤ C0 := 𝔖 𝔊
  have hR0 : CR ≤ C0 := 𝔞 𝔇 𝔊
  have hP0 : CP ≤ C0 := 𝔖 𝔇
  have hH0 : CH ≤ C0 := (𝔖 𝔇).trans 𝔇
  have hB0 : CB ≤ C0 := (𝔞 𝔇 𝔇).trans 𝔇
  have heG0 : e0 ≤ eG := 𝔞 𝔉 𝔉
  have heR0 : e0 ≤ eR := 𝔞 𝔉 𝔗
  have heP0 : e0 ≤ eP := 𝔈 𝔉
  have heH0 : e0 ≤ eH := 𝔈 $ 𝔈 𝔉
  have heB0 : e0 ≤ eB := 𝔈 $ 𝔈 𝔗
  refine ⟨C0,e0,hCG.trans hG0,lt_min (lt_min heG heR) $ lt_min heP $ lt_min heH heB ,?_⟩
  intro k D M q hk0 horder hk hD hq hM Cfr c0 ell N mu cf hfr hell hellN hcf heta htau hnu hFine
    Rbound hI V hV j h n x hx
  letI := hk0
  letI := horder
  let lam := spatialInterpolationLambda d
  let R := 𝔘 lam ell N mu
  let eta := 𝔒
  let c := 𝖯
  let U := 𝔔
  let p := fun i : Fin n => 𝙾 $ x i
  let g := fun i : Fin n => 𝔜 highLocalFieldWithout D eta c j $ x i
  let w := fun i : Fin n => 𝔜 highPeriodicTensor j $ x i
  let Chi := 𝔟 highSeparatedScoreExponentialConstant
  have hellp := lt_of_lt_of_le zero_lt_one hell
  have hfr1 := hCG.trans $ hG0.trans hfr
  have H := 𝔐 hguards  𝖡₃  hM Cfr lam ell N mu cf
    (hG0.trans hfr) hellp hellN hcf (heta.trans heG0) h
  have G := completeSourceRows_guards C k D M q hD  𝖡₃  hM Cfr lam ell N mu hfr1 hellp hellN
  rcases n with _|_|_|n
  · have hz (y : Fin 0 → Fin 3) := (𝔐 hresponse  𝖡₃  hM Cfr lam ell N mu cf
      (hR0.trans hfr) hellp hellN hcf (heta.trans heR0) V hV j h 0 x hx y).2 𝖡₃
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro y _
    change highUnionSourceMarkedNumerator C R 0 Q.a V eta j h x y^2 = 0
    grind
  · have hz (y : Fin 1 → Fin 3) := (𝔐 hresponse  𝖡₃  hM Cfr lam ell N mu cf
      (hR0.trans hfr) hellp hellN hcf (heta.trans heR0) V hV j h 1 x hx y).2 𝖡₃
    apply le_of_eq
    apply Finset.sum_eq_zero
    simpa
  · obtain ⟨had,hab⟩ := 𝗌₁
    have hM2 : 𝗜₁ := by exact_mod_cast (𝚀₁ hM).1
    have hpi (i : Fin 2) :=
      𝘄₁
    have hUi (i : Fin 2) := 𝔜 highLocalCoordinates_abs_le_one j $ x i
    have hf (i : Fin 2) :=
      H.regression_abs j (c j) (H.coefficient_ball j) $ x i
    have he (y : Fin 2 → Fin 3) : 𝔙 x y =
        𝔅 := by
      have hp := 𝔐 hpair hq hM Cfr lam ell N mu cf
        (hP0.trans hfr) hellp hellN hcf (heta.trans heP0) V hV j h x hx y
      have hfine := 𝔛 finePairThreeRow_count_two_numerator  𝖡₃  hM2 hq Cfr Q.a V eta  𝖡₄  U hUi p hpi g w (c j) y
      exact hp.trans hfine.symm
    have hcap := 𝔛 finePairCountTwoRawNumerator_sum_square_le_geometry  𝖡₃  hM2 hq Cfr Q.a V eta Q.ρ  𝖡₄  Q.a_pos Q.ρ_pos.le U hUi
      p g w hpi (fun i => H.weight_abs j $ x i ) (c j) hf
    change 𝔍 ≤
      finePairCountTwoGeometryEnvelope (C.densityUpper-𝔏⁻¹) Q.a Q.ρ eta N U
    have hs : 𝔍 =
        ∑ y : Fin 2 → Fin 3, 𝔅^2 := by
      unfold selectedRawSquareEnergy
      apply Finset.sum_congr $ by ext y; simp
      intro y _
      rw [he]
    grind
  · by_cases hnD : 𝔎 ≤ D
    · change 𝔄
      rw [if_pos hnD]
      exact 𝔐 hhigher  𝖡₃  hM Cfr c0 ell N mu cf
        (hH0.trans hfr) hell hellN hcf (heta.trans heH0) htau hnu hFine Rbound hI V hV j h 𝔎  𝖡₃  hnD x hx
    · change 𝔄
      rw [if_neg hnD]
      apply crude_raw_square_energy_pointwise Chi eta $ highRowTotalMass R.rowMass
      · exact (𝔟 highSeparatedScoreExponentialConstant_pos).le
      · exact G.total_positive.le
      bound
