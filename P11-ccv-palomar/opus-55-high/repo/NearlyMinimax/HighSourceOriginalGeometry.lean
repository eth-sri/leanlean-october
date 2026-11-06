module

public import NearlyMinimax.HighCompleteGeometry
public import NearlyMinimax.HighSourceOriginalPair
public import NearlyMinimax.HighUnionFisher
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! The higher-count universal geometry envelope dominates the actual
canonical complete source in the original periodic-frame model. Response
and coefficient legality are derived, rather than supplied as assumptions. -/
𝚫
𝚪
𝚨
𝚩
𝛈
𝚬
𝚿

 set_option hygiene false
𝗇 𝔈 𝖧
𝗇 𝔄 completeSourceRawNumerator (C.densityLower+1/𝔈) (C.densityUpper-1/𝔈) lam ell N mu D M q Cfr Q.a V eta U p g w (c j) y
𝗇 𝔅 cf*𝙦^(-C.smoothness)
𝗇 𝔇 highUnionSourceRawNumerator C R n Q.a V eta h j
𝗇 𝔉 higherBandTargetScale d 𝙳 N mu
𝗇 𝔊 𝘐
𝗃 𝔑 ἀ d k
𝗇 𝔍 𝔑 highPatchProductChart j x
𝗇 𝔎 𝖻
𝗃 𝔏 ἀ k D M q hk0 horder hk hD hq hM Cfr lam ell N mu cf
𝗃 𝔐 fun i => ἀ j $ x i
𝗃 𝔒 ἀ _ _
theorem completeSource_original_higher_geometry [NeZero d]
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) :
    ∃ Cfr0 eta0 : ℝ, 𝚣₂ ∧ 𝖴₁ ∧
      ∀ k D M q : ℕ, ∀ (_ : NeZero k), ∀ (_ : LinearOrder 𝔑 HighWindowLabels),
      𝗑 → 𝗕 → 𝗘 → highCenterResolutionThreshold C ≤ 𝔈 →
      ∀ Cfr c0 ell N mu cf : ℝ, Cfr0 ≤ Cfr → 𝗲₁ → 𝘈₂ → 𝚐₁ →
      𝔅 ≤ eta0 →
      𝙲 M ≤ c0 →
      (∀ j : Fin 𝔊, 0 < 𝔉) →
      (∀ j : Fin 𝔊, ell < 𝔉 → 𝙳 ≤ M) →
      ∀ Rbound : ℕ, (∀ r ∈ 𝗊₁, 𝘗 ∧ r ≤ Rbound) →
      ∀ V : ℝ, |𝖮₂| ≤ Q.ρ → ∀ j : 𝔑 HighWindowLabels,
      ∀ h ,
      ∀ n : ℕ, 𝖬₂ → 𝖠₁ → ∀ x ,
      (∀ i, x i ∈ 𝔑 highTorusPatch j) →
      let R := 𝔎 (spatialInterpolationLambda d) ell N mu
      let eta := 𝔅
      selectedRawSquareEnergy 𝔇 x ≤
        completeSourceHigherGeometryEnvelope (D := D) C.densityLower C.densityUpper c0 ell N mu
          M Rbound q Cfr Q.a Q.ρ eta 𝔍 := by
  obtain ⟨CfrG,etaG,hfrG,hetaG,hguards⟩ := completeSource_original_local_guards C Q
  obtain ⟨CfrR,etaR,hfrR,hetaR,hresponse⟩ := completeSource_original_response_exact_and_low_counts C Q
  refine ⟨max CfrG CfrR, min etaG etaR, hfrG.trans 𝔒 le_max_left, lt_min hetaG hetaR,?_⟩
  intro k D M q hk0 horder hk hD hq hM Cfr c0 ell N mu cf hfr hell hellN hcf heta htau hnu hFine
    Rbound hI V hV j h n hn hnD x hx
  letI := hk0
  letI := horder
  let lam := spatialInterpolationLambda d
  let R := 𝔎 lam ell N mu
  let eta := 𝔅
  let c := 𝖯
  let U := 𝔍
  let p := fun i : Fin n => 𝙾 $ x i
  let g := fun i : Fin n => 𝔑 highLocalFieldWithout D eta c j $ x i
  let w := fun i : Fin n => 𝔑 highPeriodicTensor j $ x i
  have hfrg := (le_max_left CfrG CfrR).trans hfr
  have hfrr := (le_max_right CfrG CfrR).trans hfr
  have hfr1 := hfrG.trans hfrg
  have heG := heta.trans 𝔒 min_le_left
  have heR := heta.trans 𝔒 min_le_right
  have hellp : 𝚁₁ := lt_of_lt_of_le zero_lt_one hell
  have H := 𝔏 hguards hfrg hellp hellN hcf heG h
  have G := 𝖠 ell N mu hfr1 hellp hellN
  obtain ⟨had,hab⟩ := high_source_interval_numeric C 𝔈 hM
  have hUi (i : Fin n) (l : Fin d) : |𝚅| ≤ 2 :=
    (𝔑 highLocalCoordinates_abs_le_one j (x i) l).trans 𝖠₄
  have hpi (i : Fin n) :=
    𝘄₁
  have hp (f : ℝ) hf (u : Fin 3) :=
    Q.c_pos.le.trans $ (Q.legal f V hf hV).2.2.1 u
  have hcap := completeSourceRawNumerator_higher_square_le_geometry C.densityLower C.densityUpper c0 ell N mu
    C.densityLower_pos hell D M Rbound q (by simpa only [one_div] using hab) htau hn hnD hq hnu hFine hI Cfr Q.a V eta Q.ρ
    hfr1 Q.a_pos H.amplitude_nonneg Q.ρ_pos.le H.amplitude_half U hUi p g w (by simpa only [one_div] using hpi)
    𝔐 H.without_abs 𝔐 H.weight_abs (c j) (H.coefficient_ball j) hp
  have he y : 𝔇 x y =
      𝔄 :=
    (𝔏 hresponse hfrr hellp hellN hcf heR
      V hV j h n x hx y).1
  have hs : selectedRawSquareEnergy 𝔇 x =
      ∑ y : 𝙈, 𝔄^2 := by
    unfold selectedRawSquareEnergy
    apply Finset.sum_congr $ by ext y; simp
    intro y _
    rw [he]
  exact hs.trans_le $ by simpa only [one_div] using hcap
