module

public import NearlyMinimax.HighCompletePathRisk
public import NearlyMinimax.HighPathBudget
public import RoughRegime.Macro
public import RoughRegime.Notation


public section

/-! Flexible complete-source path and cost bounds. A requested fixed frame
threshold is imposed before the extension domain and statistical parameters. -/
𝚴
𝚮
𝚨
𝚬
attribute [local irreducible] highUnionSourceDensity highUnionSourceRegression highUnionSourceState
  historyMarkedPrior massPowerNormalizer highRawDensityMass highMarginalRealScore highRealSampleKernel

𝗇 𝔄 𝚐
𝗃 𝕮 ἀ t h
𝗇 𝔨 𝕮 H j r
𝗃 𝔭 ἀ d k
𝗃 𝔮 ἀ C R
𝗇 𝔷 Q.v-eta^2*t
𝗇 𝔅 ∀ h j r x, (∀ i, x i ∈ 𝔭 highTorusPatch j) → selectedRawSquareEnergy (𝔮 highUnionSourceRawNumerator r Q.a 𝔷 eta h j) x ≤ 𝔨 (𝔭 highPatchProductChart j x)
𝗇 𝔇 fun i j => j ∈ 𝔭 highNeighborLabels i
𝗃 𝕯 (ἀ : ℝ)
𝗇 𝔈 𝕯 M
𝗇 𝔉 fun {_ _} h => 𝔭 highNeighborLabels_symmetric _ _ h
𝗇 𝔊 ∫ z, Score t z ^2 ∂P t
𝗇 𝔍 fun h => highRawDensityMass $ p h
𝗇 𝔎 t ∈ 𝗺
𝗇 𝔏 𝔷
𝗃 𝕰 ἀ C k D M q Cfr lam ell N mu
𝗇 𝔐 𝕰 completeSourceRows
𝗇 𝔑 8*𝔭 highHistoryMassParameter C.densityLower C.densityUpper
𝗇 𝔒 ℝ → Ω → 𝔭 HighWindowLabels → 𝗖
𝗇 𝔓 𝕰 HighCompleteSourceHistory
𝗇 𝕬 𝗸*𝖫₁
𝗇 𝔔 𝕬/(2+T*Real.sqrt B)^2
𝗃 𝕱 ἀ _ _
𝗇 𝔖 𝕱 le_max_left
𝗇 𝔗 𝖠 ell N mu hCfr hell hellN
𝗇 𝔘 𝗰₁
𝗇 𝔚 ∀ h j r u, 0 ≤ 𝔨 u
𝗃 𝕲 ἀ T hT Q.a Q.v eta Q.a_pos.ne' p F hF hqNonneg
𝗇 𝔛 𝕲 highNormalizedParameterPath_apply t ht h
𝗃 𝔬 ἀ t ht
𝗇 𝔜 fun t ht => (𝔬 hfisher).1
𝗇 𝔞 fun t ht => (𝔬 hfisher).2
𝗃 𝕸 𝔮 ἀ G
𝗇 𝔟 𝕸 highUnionSourceDensity_coarse_interval
𝗇 𝔠 cf*𝕯 k^(-C.smoothness)
𝗇 𝔡 𝔭 highSourceSpatialSeries n C.densityLower Q.c 𝕮 H
𝗇 𝔢 𝔬 hV
𝗇 𝔤 cm/𝔈
𝗃 𝔫 ἀ C hD hq hM Cfr lam ell N mu hCfr hell hellN
𝗇 𝔥 𝔫 completeSourceMass_prior_law T hT hsmall
𝗇 𝔦 ∫ t in (𝙋)..T, Real.sqrt 𝔊
𝗇 𝔧 𝕲 highNormalizedParameterPath
𝗇 𝔩 (𝔄:ℕ)
𝗇 𝔪 2*Real.exp (-𝔤^2/𝔑)
𝗇 𝔯 𝙰^2
𝗇 𝔱 𝗺
𝗇 𝔲 div_nonneg G.total_positive.le (𝘗₁).le
𝗇 𝔳 massPowerTilt (ν t) 𝔍 n
𝗇 𝔴 (1:ℕ) ≤ 3
𝗃 𝕭 0 ≤ ἀ
𝗃 𝕳 ἀ $ C.withDomain U
𝗃 𝕴 ∀ t ∈ ἀ, 𝔚
𝗃 𝕵 ∀ t ∈ ἀ, 𝔅
𝗃 𝕶 (ENNReal.ofReal_le_ofReal $ sub_le_sub_right ἀ _ ).trans hh
/-- All constants imposing model legality and the response floor are fixed
before the extension domain and every statistical parameter. The only energy
inputs are genuine raw local numerator envelopes and their factorial sum. -/
theorem highCompleteSource_minimax_path_bound_uniform_above [NeZero d]
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) (CfrMin : ℝ) :
    ∃ Cfr eta0 : ℝ, 𝗹 ∧ CfrMin ≤ Cfr ∧ 𝖴₁ ∧
      ∀ U : ExtensionDomain d, ∀ k D M q : ℕ,
      ∀ (_ : NeZero k) (_ : LinearOrder 𝔭 HighWindowLabels),
      ∀ hk : 𝗑, ∀ hD : 𝗕, ∀ hq : 𝗘,
      ∀ hM : highCenterResolutionThreshold C ≤ 𝔈,
      ∀ lam ell N mu : ℝ, ∀ hell : 𝚁₁, ∀ hellN : 𝘈₂,
      let R := 𝔐
      let Ω := 𝔓
      ∀ cf : ℝ, 𝕭 cf → 𝙵₂ →
      let eta := 𝔠
      eta ≤ eta0 →
      ∀ cm : ℝ, 𝕭 cm → 𝘉₂ →
      ∀ n : ℕ, ∀ T B : ℝ, ∀ hT : 𝕭 T, 𝕭 B →
      T*𝔘/historyReferenceRho 𝔄 ≤
        1/(2+8*𝕯 𝔩^2) →
      eta^2*T ≤ Q.ρ →
      𝔑*𝕯 n ≤ 𝔤 →
      ∀ H : 𝔒,
      (∀ t ∈ 𝔱, ∀ h j r, Integrable 𝔨
        $ Measure.pi fun _ : Fin r => 𝖪 ) →
      𝕴 𝔱 →
      𝕵 𝔱 →
      (∀ t ∈ 𝔱, ∀ h, 𝔡 ≤ B) →
      ENNReal.ofReal (𝔔-
        𝔯 *
          𝔪) ≤
        𝕳 minimaxRisk n := by
  obtain ⟨Cfm,etam,hCfm,hetam,hmodel⟩ := highUnionSource_original_model_uniform C Q
  obtain ⟨Cfq,etaq,hCfq,hetaq,hfloor⟩ := highUnionSource_ternary_floor_uniform C Q
  let Cfr := max (max Cfm Cfq) CfrMin
  let eta0 := min etam etaq
  have hCfr : 𝗹 := (hCfm.trans 𝔖).trans 𝔖
  have hCfmfr : Cfm ≤ Cfr := (𝔖).trans 𝔖
  have hCfqfr : Cfq ≤ Cfr := (𝕱 le_max_right).trans 𝔖
  have heta0 : 𝖴₁ := lt_min hetam hetaq
  refine ⟨Cfr,eta0,hCfr,𝕱 le_max_right,heta0,?_⟩
  intro U k D M q hk0 horder hk hD hq hM lam ell N mu hell hellN
  letI := hk0
  letI := horder
  let R := 𝔐
  let Ω := 𝔓
  let E := SourceRowMark d D M q (C.densityLower+1/𝔈) (C.densityUpper-1/𝔈) Cfr lam ell N mu
  have G := 𝔗
  have hpos := completeSourceRows_mass_positive (k := k) C hD hq hM Cfr lam ell N mu hCfr hell hellN
  letI : 𝗄₁ := highUnionMark_standardBorel
  letI := 𝕸 highUnionSourceLaw_probability
  dsimp only
  intro cf hcf hcfH
  let eta := 𝔠
  intro heta cm hcm hcmU n T B hT hB hsmall hVbudget heps H hH hH0 hdom hbudget
  let p := 𝔮 highUnionSourceDensity
  let F := 𝔮 highUnionSourceRegression eta
  have hp : 𝘍 := 𝕸 highUnionSourceDensity_joint_measurable
  have hF : 𝗴 := 𝕸 highUnionSourceRegression_joint_measurable eta
  let π := 𝗛
  let act := 𝗾
  let Ba := 𝔘
  let ν (t : ℝ) := historyMarkedPrior 𝔇 𝔄 t π act
  have hBa : 𝕭 Ba := 𝔲
  have hν (t : ℝ) (ht : 𝔎) : IsProbabilityMeasure $ ν t :=
    𝔫 completeSourcePrior_probability T hT hsmall t ht
  have hV (t : ℝ) (ht : 𝔎) : |𝔏-Q.v| ≤ Q.ρ := by
    simp only [sub_sub_cancel_left,abs_neg,abs_mul,abs_of_nonneg $ sq_nonneg eta ,abs_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_left ht.2 $ sq_nonneg eta ).trans hVbudget
  have hqFloor (t : ℝ) (ht : 𝔎) (h : Ω) (x : Covariate d) (y : Fin 3) :=
    hfloor k D hk0 horder hk _ inferInstance E inferInstance R 𝔈
      (G.mono_frame hCfq hCfqfr) cf hcf
      (heta.trans 𝕱 min_le_right) h _ 𝔢 x y
  have hqPos (t : ℝ) (ht : 𝔎) (h : Ω) (x : Covariate d) (y : Fin 3) := Q.c_pos.trans_le $ 𝔬 hqFloor h x y
  have hqNonneg := fun t ht h x y => (𝔬 hqPos h x y).le
  let θ := 𝔧
  let bad : ℝ → Set Ω := fun _ => {h | 𝔤 < |𝔮 highUnionSourceMass h-1|}
  let eps := 𝔪
  have hm : Measurable 𝔮 highUnionSourceMass := 𝕸 highUnionSourceMass_measurable
  have hbad (t : ℝ) (_ : 𝔎) : MeasurableSet $ bad t :=
    measurableSet_lt measurable_const (hm.sub_const 1).abs
  have hlegal (t : ℝ) (ht : 𝔎) (h : Ω) (hh : h ∉ bad t) :
      𝕳 Admissible 𝕮 θ := by
    have hgood : |𝔮 highUnionSourceMass h-1| ≤ 𝔤 := le_of_not_gt hh
    obtain ⟨_,hlegal⟩ := hmodel U k D hk0 horder hk _ inferInstance E inferInstance inferInstance
      R 𝔈 (G.mono_frame hCfm hCfmfr) cf hcf hcfH
      (heta.trans 𝕱 min_le_left) cm hcm hcmU h hgood _ 𝔢
    change 𝕳 Admissible
      𝕮 𝔧
    rw [𝔛]
    exact hlegal
  have hmassEq : 𝔍 = 𝔮 highUnionSourceMass := by
    funext h
    simp only [p,highRawDensityMass,highUnionSourceMass]
  have hmass (t : ℝ) (ht : 𝔎) :
      Measure.map 𝔍 (ν t) =
      Measure.map 𝔍 (ν 0) := by
    have h1 := 𝔬 𝔥
    have h0 := 𝔥 0 ⟨le_rfl,hT⟩
    rw [hmassEq]
    exact h1.trans h0.symm
  have hbadmass (t : ℝ) (ht : 𝔎) :
      (𝔳).real (bad t) ≤ eps := by
    rw [hmassEq]
    exact 𝔫 completeSourceMass_prior_tilted_tail
       𝖡₃  T hT hsmall n 𝔤 heps t ht
  have hfisher (t : ℝ) (ht : 𝔎) := by
    letI := 𝔬 hν
    exact 𝕸 highUnionSource_raw_fisher_bound hpos (ν t) n hk Q.a 𝔏 eta Q.c
      Q.a_pos.ne' Q.c_pos 𝔬 hqFloor
      (fun j h x => 𝔫 completeSourceDensity_product_zero j h n x)
      (H t) 𝔬 hH 𝔬 hH0 𝔬 hdom B hB 𝔬 hbudget
  have hactm := highUnionActivation_measurable R G.activation_measurable $ highCenterMix C
  have hact := 𝕸 highUnionSourceActivation_centered hpos
  have hab := 𝕸 highUnionSourceActivation_bound hpos
  have hh := historyMarkedPrior_original_minimax_path_bound
    𝔇 𝔭 highNeighborLabels_self_mem
    𝔉 𝔄
    (one_le_pow₀ (by norm_num : 𝔴)) 𝔭 highNeighbor_dependency_card
    π act hactm hact Ba T hBa hT hab hsmall (C.withDomain U) n Q.a Q.v eta
    C.densityLower C.densityUpper B eps Q.a_pos C.densityLower_pos p F hp hF
    𝔟 hqPos hmass θ
    (fun t ht h => 𝔛)
    (fun t ht => Q.effective_interval 𝔢) bad hbad hlegal hbadmass
    𝔜 𝔞
  let P (t : ℝ) := highRealSampleKernel n Q.a 𝔏 p F hp hF ∘ₘ
    𝔳
  let Score (t : ℝ) := highMarginalRealScore 𝔇
    𝔉
    (ν t) π act n Q.a 𝔏 eta p F
  letI := historyMarkedReference_probability 𝔇
    𝔭 highNeighborLabels_self_mem
    𝔉 𝔄
    (one_le_pow₀ (by norm_num : 𝔴)) 𝔭 highNeighbor_dependency_card π
  have hInt := highHistoryScore_sqrt_energy_intervalIntegrable
    𝔇
    𝔉 𝔄 π act hactm
    Ba hBa hab n Q.a Q.v eta C.densityLower C.densityUpper T B Q.a_pos C.densityLower_pos
    hT p F hp hF hν 𝔟 hqPos
    𝔜 𝔞
  have henergy (t : ℝ) (ht : 𝔎) : 𝔊 ≤ B := by
    letI := 𝔬 hν
    exact ((𝕱 highMarginalRealScore_memLp_energy (ν t) π act hactm Ba hBa hab n Q.a
      𝔏 eta C.densityLower C.densityUpper Q.a_pos C.densityLower_pos
      p F hp hF 𝔟 𝔬 hqPos
      (𝔬 hfisher).1).2).trans (𝔬 hfisher).2
  have hscore := intervalIntegral_sqrt_energy_le
    (fun t => 𝔊) T B hT hInt henergy
  have hsc0 : 𝕭 𝔦 :=
    intervalIntegral.integral_nonneg hT fun _ _ => Real.sqrt_nonneg _
  have hfrac : 𝔔 ≤
      𝕬/(2+𝔦)^2 := by
    apply div_le_div_of_nonneg_left  𝖠₃  𝖠₃
    exact (sq_le_sq₀  𝖡₄  𝖠₃ ).mpr 𝖡₄
  have hout := 𝕶 hfrac
  simpa only [ModelConstants.withDomain,effectiveVarianceUpper] using hout


 set_option hygiene false
𝗇 𝔙 𝗋
𝗇 𝔣 𝔩*𝔙*E
𝗇 𝔰 𝖿
𝗇 𝔵 Icc 0 delta
𝗇 𝔶 𝔙*E
𝗃 𝕷 ἀ (Nat.cast_nonneg _) _
theorem highCompleteSource_cost_risk_uniform_above {d : ℕ} [NeZero d]
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) (CfrMin : ℝ) :
    ∃ Cfr eta0 ctr : ℝ, 𝗹 ∧ CfrMin ≤ Cfr ∧ 𝖴₁ ∧ 0 < ctr ∧
      ∀ U : ExtensionDomain d, ∀ k D M q : ℕ,
      ∀ (_ : NeZero k) (_ : LinearOrder 𝔭 HighWindowLabels),
      ∀ hk : 𝗑, ∀ hD : 𝗕, ∀ hq : 𝗘,
      ∀ hM : highCenterResolutionThreshold C ≤ 𝔈,
      ∀ lam ell N mu : ℝ, ∀ hell : 𝚁₁, ∀ hellN : 𝘈₂,
      let R := 𝔐
      let Ω := 𝔓
      ∀ cf : ℝ, 𝕭 cf → 𝙵₂ →
      let eta := 𝔰
      eta ≤ eta0 →
      ∀ cm : ℝ, 𝕭 cm → 𝘉₂ →
      ∀ n : ℕ, ∀ E : ℝ, 𝕭 E →
      𝔑*n ≤ cm/M →
      let Bl := 𝔘
      let c := highPathConstant 𝔄 Q.ρ eta0
      let I := Real.sqrt 𝔣
      let delta := localScorePathLength c Bl I
      ∀ H : 𝔒,
      (∀ t ∈ 𝔵, ∀ h j r, Integrable 𝔨
        $ Measure.pi fun _ => 𝖪 ) →
      𝕴 𝔵 →
      𝕵 𝔵 →
      (∀ t ∈ 𝔵, ∀ h,
        𝔡 ≤ 𝔣) →
      ENNReal.ofReal (ctr*𝗸/(𝘄₂+𝔶)-
        𝔯 *
          (2*Real.exp (-(cm/M)^2/𝔑))) ≤
        𝕳 minimaxRisk n := by
  obtain ⟨Cfr,eta0,hCfr,hmin,heta0,hpath⟩ := highCompleteSource_minimax_path_bound_uniform_above C Q CfrMin
  let c := highPathConstant 𝔄 Q.ρ eta0
  have hc := highPathConstant_pos 𝔄 Q.ρ_pos heta0
  let ctr := 𝗆₂/(3*𝔩*(2+c)^2)
  have hctr : 0 < ctr := div_pos (sq_pos_of_pos hc) 𝖠₃
  refine ⟨Cfr,eta0,ctr,hCfr,hmin,heta0,hctr,?_⟩
  intro U k D M q hk0 horder hk hD hq hM lam ell N mu hell hellN
  letI := hk0
  letI := horder
  let R := 𝔐
  have G := 𝔗
  dsimp
  intro cf hcf hcfH heta cm hcm hcmU n E hE heps H hH hH0 hdom hbudget
  let eta := 𝔰
  let Bl := 𝔘
  let I := Real.sqrt 𝔣
  let delta := localScorePathLength c Bl I
  have hBl := 𝔲
  have hI : 𝕭 I := Real.sqrt_nonneg _
  have hdelt := localScorePathLength_pos hc hBl hI
  have hnumE : 𝕭 𝔶 := mul_nonneg 𝕷 pow_nonneg hE
  have hbudget0 : 𝕭 𝔣 := 𝖠₃
  have hsmall := highPath_update_budget 𝔄 Q.ρ_pos heta0 hBl hI
  have heta0' : 𝕭 eta := mul_nonneg hcf 𝕷 Real.rpow_nonneg
  have hV := highPath_variance_budget 𝔄 Q.ρ_pos heta0 hBl hI heta0' heta
  have hh := hpath U k D M q hk0 horder hk hD hq hM lam ell N mu hell hellN
    cf hcf hcfH heta cm hcm hcmU n delta 𝔣 hdelt.le hbudget0
    hsmall hV heps H hH hH0 hdom hbudget
  have hIE : I^2 = 𝔩*𝔶 := by
    grind
  have hn := score_cost_scaled_numeric (eta := eta) hc hBl hI (mul_nonneg hdelt.le hI)
     le_rfl  𝖥₄  hnumE hIE
  have hout := 𝕶 hn
  exact hout
