module

public import NearlyMinimax.CompleteSaddleGeometry
public import NearlyMinimax.CompleteSaddleEnergyGuards
public import NearlyMinimax.CompleteGeometryEnergyAssembly
public import NearlyMinimax.LowerRawCostReduction
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Actual full-count geometry energy at the canonical rounded saddle.
The constants are numerical model data and precede the saddle shift. -/
𝛅
𝚶
𝚨
𝚩
𝛈
𝚬

 def completeSaddleScoreFactor {d : ℕ} (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) : ℝ :=
  highFixedScoreDenominator C.densityLower Q.c*𝙉^d
 set_option hygiene false
𝗇 𝔈 𝙊
def completeSaddleDegreeFactor (d : ℕ) : ℝ := (𝔈+8)/4+1
 set_option hygiene false
𝗇 𝔅 lowerSaddleResponseOrder C.smoothness d
𝗇 𝔇 completeSaddleScoreFactor C Q
def completeSaddleOrdinaryConstant {d : ℕ} (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) (Cfr : ℝ) : ℝ :=
  ordinaryFineAliasFactorialConstant C.smoothness d 𝔅
    C.densityLower C.densityUpper Cfr Q.a Q.ρ 𝔇
 def completeSaddleDefectConstant {d : ℕ} (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) (Cfr : ℝ) : ℝ :=
  completeGeometryDefectConstant d 𝔅 C.densityUpper Cfr Q.a Q.ρ
    𝔇
 set_option hygiene false
𝗃 𝔍 ἀ d 𝔅 C.densityLower C.densityUpper Cfr Q.a Q.ρ $ completeSaddleC0 C
def completeSaddleFieldConstant {d : ℕ} (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) (Cfr : ℝ) : ℝ :=
  𝔍 completeGeometryFieldConstant 𝔇
 set_option hygiene false
𝗃 𝔊 ἀ C Q Cfr
def completeSaddleAliasConstant {d : ℕ} (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) (Cfr : ℝ) : ℝ :=
  𝔍 completeGeometryAliasConstant (completeSaddleDegreeFactor d) 𝔇 𝔊 completeSaddleOrdinaryConstant
 𝗇 𝔏 𝙪₂
def completeSaddleExteriorConstant {d : ℕ} (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) : ℝ :=
  completeGeometryExteriorConstant d 𝔇
    𝔏

 𝗇 𝔐 𝙲
𝗃 𝔔 completeSourceSaddleActivity C ἀ Cfr (spatialInterpolationLambda d) Cω n
𝗃 𝔖 ἀ C.smoothness d (highCompleteSourceSaddleCoefficient C) (highCompleteSourceSaddleTheta C) Cω
def completeSaddleEnergyBudget {d : ℕ} (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C)
    (Cfr cf Cω : ℝ) (n : ℕ) : ℝ :=
  𝔖 lowerSaddleRawEnergyBound cf 𝔊 completeSaddleDefectConstant
    𝔊 completeSaddleAliasConstant 𝔊 completeSaddleFieldConstant (completeSaddleExteriorConstant C Q)
    𝔔 𝔅
    𝔐 n

 theorem completeSaddleScoreFactor_pos {d } (C : ModelConstants d) Q :
    0 < 𝔇 := by
  unfold completeSaddleScoreFactor highFixedScoreDenominator
  positivity [C.densityLower_pos, Q.c_pos]
 theorem completeSaddleDefectConstant_pos {d } (C : ModelConstants d) Q Cfr :
    0 < 𝔊 completeSaddleDefectConstant := completeGeometryDefectConstant_pos ..
 theorem completeSaddleAliasConstant_pos {d } (C : ModelConstants d) Q Cfr :
    0 < 𝔊 completeSaddleAliasConstant := completeGeometryAliasConstant_pos ..
 theorem completeSaddleFieldConstant_pos {d } (C : ModelConstants d) Q Cfr :
    0 < 𝔊 completeSaddleFieldConstant := completeGeometryFieldConstant_pos ..
 theorem completeSaddleExteriorConstant_pos {d } (C : ModelConstants d) Q :
    0 < completeSaddleExteriorConstant C Q := completeGeometryExteriorConstant_pos ..

 𝗁 𝔗 x x d (highCompleteSourceSaddleCoefficient C) (highCompleteSourceSaddleTheta C) Cω n
theorem completeSaddleEnergyBudget_nonneg {d } (C : ModelConstants d) Q
    Cfr cf Cω n : 0 ≤ 𝔊 completeSaddleEnergyBudget cf Cω n := by
  unfold completeSaddleEnergyBudget lowerSaddleRawEnergyBound
  have h5 := (𝔊 completeSaddleDefectConstant_pos).le
  have h6 := (𝔊 completeSaddleAliasConstant_pos).le
  have h7 := (𝔊 completeSaddleFieldConstant_pos).le
  have hch := (completeSaddleExteriorConstant_pos C Q).le
  have hN := 𝔖 lowerSaddleN_positive 𝔐 n
  have hmu : 0 ≤ 𝔗 lowerSaddleMu := by
    unfold lowerSaddleMu
    positivity [𝔗 lowerSaddleH_positive]
  positivity

 set_option hygiene false
𝗇 𝔉 𝖧⁻¹
𝗇 𝔒 C.densityLower+𝔉
𝗇 𝔓 C.densityUpper-𝔉
𝗇 𝔄 (𝔒+𝔓)/ (𝔓-𝔒)
𝗇 𝔎 𝖦₁+j
𝗇 𝔑 𝙋<1
𝗃 𝔘 ἀ C n
theorem eventually_completeSaddleGeometry_factorial {d : ℕ} [NeZero d]
    C Q (hs : 𝘎)
    (hd : 𝘊 < 𝔈) {cf : ℝ} (hcf : 𝙻₁) Cfr Cω :
    ∀ᶠ n : ℕ in atTop,
       ∑ r ∈ Finset.range 𝗉, poissonCountWeight
        (𝔇*completeSaddleMu C Cω n) r *
        ∫ U, 𝔊 completeSaddleGeometryEnvelope cf Cω n r U ∂𝗾₂ ≤
          𝔊 completeSaddleEnergyBudget cf Cω n := by
  have hCs := (completeSaddleScoreFactor_pos C Q).le
  have hd5 : 𝘚 := by
    have h : 𝗦<d := 𝖡₄
    aesop
  have hbd := (zero_lt_one.trans C.one_lt_densityUpper).le
  have hCal : 0 ≤ 𝔍 finePairSaddleAliasFactorialConstant (completeSaddleDegreeFactor d)
        (3*𝔇) := by
    unfold finePairSaddleAliasFactorialConstant aliasTailConstant
    have hP := 𝔍 finePairUniformSpatialPrefactor_nonneg
    have hI := spatialInverseFourConstant_nonneg d
    have hB := finePairAliasGeometricBase_nonneg d C.densityUpper
    positivity
  filter_upwards [eventually_completeSaddleEnergyGuards C hs hd hcf Cω,
    tendsto_natCast_atTop_atTop.eventually $ eventually_ordinaryFineAliasSaddleGeometryEnvelope_factorial_tail
      hs hd C.densityLower_pos (C.densityLower_lt_one.trans C.one_lt_densityUpper) Cω cf
      𝔅 Cfr Q.a Q.ρ 𝔇 hCs ,
    tendsto_natCast_atTop_atTop.eventually $ eventually_completeSourceSaddle_parameters C hs hd hcf
      (by norm_num : 𝔑) (by norm_num : 𝔑) Cω ] with n G hO hphysical
  let M := 𝔘 completeSaddleM
  let D := 𝔘 completeSaddleD
  let q := 𝔅
  let N := completeSaddleN C Cω n
  let mu := completeSaddleMu C Cω n
  let ell := completeSaddleEll C Cω n
  let eta := completeSaddleEta C Cω cf n
  let tau := 𝔘 completeSaddleTau
  let c0 := completeSaddleC0 C
  let Cs := 𝔇
  let K := completeSaddleDegreeFactor d
  let R := ordinaryFineAliasSaddleTargetBound C.smoothness d C.densityLower C.densityUpper
  let Cord := 𝔊 completeSaddleOrdinaryConstant
  let Bl := 𝔔 q
  let Chi := 𝔏
  have hD := hphysical.2.1
  have hext : exteriorTau 𝔄 = tau := by
    have h := exteriorTau_sqrt_ratio 𝔘 completeSaddleAD 𝔘 completeSaddleBD G.ad_positive G.density_interval
    simpa only [tau,completeSaddleTau,shrunkDensityExponent,densityIntervalExponent,completeSaddleAD,completeSaddleBD,one_div] using h
  have hfield : Real.exp (2*exteriorTau 𝔄*M)*(ell^(2-𝔈))^2*mu^4 ≤
      𝙺₁*N^(-𝔈) := by
    rw [hext]
    convert G.field_scale_square using 1 <;> ring
  have hOrd : ∑ j ∈ Finset.range 𝘀₂, poissonCountWeight 𝖫₂ 𝔎 *
      ∫ U, ordinaryFineAliasFamilyResponseSquareEnvelope (F := D)
        𝗊₁ M R q C.densityLower C.densityUpper c0 Cfr Q.a Q.ρ eta ell
        (fun t => higherBandTargetScale d t N mu) U ∂fullSpatialPatchDesign d 𝔎 ≤
      Cord*(𝗸*Real.exp 𝙹₁*N^(4-𝔈))*poissonCountWeight (Cord*mu) 𝖦₁ := by
    simpa only [ordinaryFineAliasSaddleGeometryEnvelope,ordinaryFineAliasSaddleCoefficient,ordinaryFineAliasSaddleTheta,
      M,D,q,N,mu,ell,eta,tau,c0,Cs,R,Cord,completeSaddleOrdinaryConstant,
      highCompleteSourceSaddleCoefficient,highCompleteSourceSaddleTheta,completeSaddleM,completeSaddleD,
      completeSaddleN,completeSaddleMu,completeSaddleEll,completeSaddleEta,completeSaddleTau,completeSaddleC0] using hO fun _ => D
  have hHigher := finite_complete_higher_geometry_energy_le hd5 hD C.densityLower C.densityUpper c0 K ell N mu
    M R q Cfr Q.a Q.ρ eta Cs _ C.densityLower_pos Q.a_pos
    (by simpa only [completeSaddleAD,completeSaddleBD,one_div] using G.density_interval) (hext.trans_le G.tau_le)
    (by linarith [densityIntervalExponent_pos C.densityLower_pos $ C.densityLower_lt_one.trans C.one_lt_densityUpper ])
    (by dsimp [K,completeSaddleDegreeFactor]; positivity) hCs G.ell_one G.ell_lt_N.le rfl G.degree_multiple
    G.mu_positive G.mu_one G.mu_log G.response_taylor hfield hOrd
  have h := completeSourceGeometryEnvelope_factorial_from_higher (NeZero.pos d) D M R q n hD
    C.densityLower C.densityUpper c0 K ell N mu Cfr Q.a Q.ρ eta Chi Bl Cs Cord tau
    (lt_of_lt_of_le zero_lt_one G.N_one) hCs G.mu_positive.le G.mu_one
    (by simpa only [completeSaddleBD,one_div] using G.bd_nonneg)  𝖢₄ 
    (zero_le_one.trans $ ordinaryFineAliasFactorialConstant_ge_one hbd hCs ) hCal G.tau_nonneg hHigher
  convert h using 1 <;> (try dsimp only [completeSaddleGeometryEnvelope,completeSaddleEnergyBudget,
    completeSaddleDefectConstant,completeSaddleAliasConstant,completeSaddleFieldConstant,completeSaddleExteriorConstant,
    lowerSaddleRawEnergyBound,completeSaddleTau,completeSaddleC0]) <;> (try simp only [poissonCountWeight]) <;> ring
