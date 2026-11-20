module

public import NearlyMinimax.HighUnionRawFisher

public import NearlyMinimax.CompleteSourceDensityProduct

public import NearlyMinimax.CompleteSourceSaddleMassTail

public import NearlyMinimax.HighPriorRisk

public import NearlyMinimax.HighParameterPath

public import NearlyMinimax.HighUnionSourceUniformModel

public import NearlyMinimax.HighUnionObservationGuards

public import NearlyMinimax.TernaryEffectiveInterval

public import NearlyMinimax.HighScoreTimeKernel

public import NearlyMinimax.HighPathBudget

@[expose] public section

/-! Flexible complete-source path and cost bounds. A requested fixed frame
threshold is imposed before the extension domain and statistical parameters. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true
attribute [local instance] Classical.propDecidable
attribute [local irreducible] highUnionSourceDensity highUnionSourceState
  historyMarkedPrior massPowerNormalizer highRawDensityMass highMarginalRealScore highRealSampleKernel

variable {d : ℕ} [NeZero d] {C : ModelConstants d} (Q : LowSmoothnessTernaryConstants C) (CfrMin : ℝ)

/-- All constants imposing model legality and the response floor are fixed
before the extension domain and every statistical parameter. The only energy
inputs are genuine raw local numerator envelopes and their factorial sum. -/
theorem highCompleteSource_minimax_path_bound_uniform_above :
    ∃ Cfr eta0 : ℝ, 1 ≤ Cfr ∧ CfrMin ≤ Cfr ∧ 0 < eta0 ∧
      ∀ U : ExtensionDomain d, ∀ k D M q : ℕ,
      ∀ (_ : NeZero k) (_ : LinearOrder (HighWindowLabels d k)),
      ∀ hk : 4 ≤ k, ∀ hD : 3 ≤ D, ∀ hq : 1 ≤ q,
      ∀ hM : highCenterResolutionThreshold C ≤ (M : ℝ),
      ∀ lam ell N mu : ℝ, ∀ hell : 0 < ell, ∀ hellN : ell < N,
      let R := completeSourceRows C k D M q Cfr lam ell N mu
      let Ω := HighCompleteSourceHistory C k D M q Cfr lam ell N mu
      ∀ cf : ℝ, 0 ≤ cf → highWindowHolderConstant C*cf ≤ C.holderBound →
      let eta := cf*(k : ℝ)^(-C.smoothness)
      eta ≤ eta0 →
      ∀ cm : ℝ, 0 ≤ cm → cm ≤ 1/C.densityUpper →
      ∀ n : ℕ, ∀ T B : ℝ, ∀ hT : 0 ≤ T, 0 ≤ B →
      T*(highRowTotalMass R.rowMass/highCenterMix C)/historyReferenceRho (3^d) ≤
        1/(2+8*((3^d:ℕ):ℝ)^2) →
      eta^2*T ≤ Q.ρ →
      8*highHistoryMassParameter d k C.densityLower C.densityUpper*(n:ℝ) ≤ cm/(M:ℝ) →
      ∀ H : ℝ → Ω → HighWindowLabels d k → (r : ℕ) → (DesignSample d r) → ℝ,
      (∀ t ∈ Icc 0 T, ∀ h j r, Integrable (H t h j r)
        (Measure.pi (fun _ : Fin r => volume.restrict (spatialPatchBox d)))) →
      (∀ t ∈ Icc 0 T, ∀ h j r u, 0 ≤ H t h j r u) →
      (∀ t ∈ Icc 0 T, ∀ h j r x, (∀ i, x i ∈ highTorusPatch j) →
        selectedRawSquareEnergy (highUnionSourceRawNumerator C R r Q.a (Q.v-eta^2*t) eta h j) x ≤
          H t h j r (highPatchProductChart j x)) →
      (∀ t ∈ Icc 0 T, ∀ h, highSourceSpatialSeries d k n C.densityLower Q.c (H t h) ≤ B) →
      ENNReal.ofReal (eta^4*T^2/(2+T*Real.sqrt B)^2-
        (effectiveVarianceUpper C-C.varianceLower)^2 *
          (2*Real.exp (-(cm/(M:ℝ))^2/(8*highHistoryMassParameter d k C.densityLower C.densityUpper)))) ≤
        minimaxRisk (C.withDomain U) n := by
  obtain ⟨Cfm,etam,hCfm,hetam,hmodel⟩ := highUnionSource_original_model_uniform Q
  obtain ⟨Cfq,etaq,hCfq,hetaq,hfloor⟩ := highUnionSource_ternary_floor_uniform Q
  let Cfr := max (max Cfm Cfq) CfrMin
  let eta0 := min etam etaq
  have hCfr : 1 ≤ Cfr := (hCfm.trans (le_max_left _ _)).trans (le_max_left _ _)
  have hCfmfr : Cfm ≤ Cfr := (le_max_left _ _).trans (le_max_left _ _)
  have hCfqfr : Cfq ≤ Cfr := (le_max_right _ _).trans (le_max_left _ _)
  have heta0  := lt_min hetam hetaq
  refine ⟨Cfr,eta0,hCfr,le_max_right _ _,heta0,?_⟩
  intro U k D M q hk0 horder hk hD hq hM lam ell N mu hell hellN
  letI := hk0
  letI := horder
  let R := completeSourceRows C k D M q Cfr lam ell N mu
  let Ω := HighCompleteSourceHistory C k D M q Cfr lam ell N mu
  let E := SourceRowMark d D M q (C.densityLower+1/(M:ℝ)) (C.densityUpper-1/(M:ℝ)) Cfr lam ell N mu
  have G := completeSourceRows_guards k hD hq hM lam mu hCfr hell hellN
  have hpos := completeSourceRows_mass_positive (k := k) C hD hq hM Cfr lam ell N mu hCfr hell hellN
  letI : StandardBorelSpace (HighUnionMark E) := highUnionMark_standardBorel
  letI := highUnionSourceLaw_probability C R G
  dsimp
  intro cf hcf hcfH
  let eta := cf*(k : ℝ)^(-C.smoothness)
  intro heta cm hcm hcmU n T B hT hB hsmall hVbudget heps H hH hH0 hdom hbudget
  let p := highUnionSourceDensity C R
  let F := highUnionSourceRegression C R eta
  have hp  := highUnionSourceDensity_joint_measurable C R G
  have hF  := highUnionSourceRegression_joint_measurable C R G eta
  let π := highUnionLaw R (highCenterMix C)
  let act := highUnionActivation R (highCenterMix C)
  let Ba := highRowTotalMass R.rowMass/highCenterMix C
  let ν (t : ℝ) := historyMarkedPrior (windowDepends d k) (3^d) t π act
  have hBa  := div_nonneg G.total_positive.le (highCenterMix_mem C).1.le
  have hν (t : ℝ) (ht : t ∈ Icc 0 T)  :=
    completeSourcePrior_probability C hD hq hM Cfr lam ell N mu hCfr hell hellN hT hsmall ht
  have hV (t : ℝ) (ht : t ∈ Icc 0 T) : |(Q.v-eta^2*t)-Q.v| ≤ Q.ρ := by
    simp [sub_sub_cancel_left,abs_neg,abs_mul,abs_of_nonneg (sq_nonneg eta),abs_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_left ht.2 (sq_nonneg eta)).trans hVbudget
  have hqFloor (t : ℝ) (ht : t ∈ Icc 0 T) (h : Ω) (x : Covariate d) (y : Fin 3)  :=
    hfloor k D hk0 horder hk _ inferInstance E inferInstance R (M:ℝ)
      (G.mono_frame hCfq hCfqfr) cf hcf
      (heta.trans (min_le_right _ _)) h _ (hV t ht) x y
  have hqPos (t : ℝ) (ht : t ∈ Icc 0 T) (h : Ω) (x : Covariate d) (y : Fin 3)  := Q.c_pos.trans_le (hqFloor t ht h x y)
  have hqNonneg := fun t ht h x y => (hqPos t ht h x y).le
  let θ := highNormalizedParameterPath hT Q.a_pos.ne' p F hF hqNonneg
  let bad : ℝ → Set Ω := fun _ => {h | cm/(M:ℝ) < |highUnionSourceMass C R h-1|}
  let eps := 2*Real.exp (-(cm/(M:ℝ))^2/(8*highHistoryMassParameter d k C.densityLower C.densityUpper))
  have hm  := highUnionSourceMass_measurable C R G
  have hbad (t : ℝ) (_ : t ∈ Icc 0 T) : MeasurableSet (bad t) :=
    measurableSet_lt measurable_const ((hm.sub_const 1).abs)
  have hlegal (t : ℝ) (ht : t ∈ Icc 0 T) (h : Ω) (hh : h ∉ bad t) :
      Admissible (C.withDomain U) (θ t h) := by
    have hgood : |highUnionSourceMass C R h-1| ≤ cm/(M:ℝ) := le_of_not_gt hh
    obtain ⟨_,hlegal⟩ := hmodel U k D hk0 horder hk _ inferInstance E inferInstance inferInstance
      R (M:ℝ) (G.mono_frame hCfm hCfmfr) cf hcf hcfH
      (heta.trans (min_le_left _ _)) cm hcm hcmU h hgood _ (hV t ht)
    change Admissible (C.withDomain U)
      (highNormalizedParameterPath hT Q.a_pos.ne' p F hF hqNonneg t h)
    rw [highNormalizedParameterPath_apply hT Q.a_pos.ne' p F hF hqNonneg ht h]
    exact hlegal
  have hmassEq : (fun h => highRawDensityMass (p h)) = highUnionSourceMass C R := by
    funext h
    simp only [p,highRawDensityMass,highUnionSourceMass]
  have hmass (t : ℝ) (ht : t ∈ Icc 0 T) :
      Measure.map (fun h => highRawDensityMass (p h)) (ν t) =
      Measure.map (fun h => highRawDensityMass (p h)) (ν 0) := by
    have h1 := completeSourceMass_prior_law C hD hq hM Cfr lam ell N mu hCfr hell hellN hT hsmall t ht
    have h0 := completeSourceMass_prior_law C hD hq hM Cfr lam ell N mu hCfr hell hellN hT hsmall 0 ⟨le_rfl,hT⟩
    rw [hmassEq]
    exact h1.trans h0.symm
  have hbadmass (t : ℝ) (ht : t ∈ Icc 0 T) :
      (massPowerTilt (ν t) (fun h => highRawDensityMass (p h)) n).real (bad t) ≤ eps := by
    rw [hmassEq]
    exact completeSourceMass_prior_tilted_tail C hD hq hM Cfr lam ell N mu hCfr hell hellN
      (by omega) hT hsmall heps ht
  have hfisher (t : ℝ) (ht : t ∈ Icc 0 T) := by
    letI := hν t ht
    exact highUnionSource_raw_fisher_bound C R G hpos (ν t) n hk Q.a (Q.v-eta^2*t) eta Q.c
      Q.a_pos.ne' Q.c_pos (hqFloor t ht)
      (fun j h x => completeSourceDensity_product_zero hD hq hM hCfr hell hellN j h x)
      (H t) (hH t ht) (hH0 t ht) (hdom t ht) B hB (hbudget t ht)
  have hactm := highUnionActivation_measurable R G.activation_measurable (highCenterMix C)
  have hact := highUnionSourceActivation_centered C R G hpos
  have hab := highUnionSourceActivation_bound C R G hpos
  have hh := historyMarkedPrior_original_minimax_path_bound
    (by bound) (highNeighbor_dependency_card d k) hactm hact hBa hT hab hsmall (C := (C.withDomain U)) (n := n) Q.a Q.v eta
    C.densityLower C.densityUpper B eps Q.a_pos C.densityLower_pos (F := F) hp hF
    (highUnionSourceDensity_coarse_interval C R G) hqPos hmass
    (fun t ht h => highNormalizedParameterPath_apply hT Q.a_pos.ne' p F hF hqNonneg ht h)
    (fun t ht => Q.effective_interval (hV t ht)) hbad hlegal hbadmass
    (fun t ht => (hfisher t ht).1) (fun t ht => (hfisher t ht).2)
  let P (t : ℝ) := (highRealSampleKernel n Q.a (Q.v-eta^2*t) (F := F) hp hF) ∘ₘ
    massPowerTilt (ν t) (fun h => highRawDensityMass (p h)) n
  let Score (t : ℝ) := highMarginalRealScore
    (ν t) π act n Q.a (Q.v-eta^2*t) eta p F
  letI := historyMarkedReference_probability
    (by bound) (highNeighbor_dependency_card d k) π
  have hInt := highHistoryScore_sqrt_energy_intervalIntegrable hactm hBa hab n B Q.a_pos C.densityLower_pos
    hT (F := F) hp hF hν (highUnionSourceDensity_coarse_interval C R G) hqPos
    (fun t ht => (hfisher t ht).1) (fun t ht => (hfisher t ht).2)
  have henergy (t : ℝ) (ht : t ∈ Icc 0 T) : (∫ z, (Score t z)^2 ∂P t) ≤ B := by
    letI := hν t ht
    exact ((highMarginalRealScore_memLp_energy hactm hBa hab Q.a_pos C.densityLower_pos (F := F) hp hF (highUnionSourceDensity_coarse_interval C R G) (hqPos t ht)
      (hfisher t ht).1).2).trans (hfisher t ht).2
  have hscore := by have h := intervalIntegral.integral_mono_on hT hInt (intervalIntegrable_const (c := Real.sqrt _)) (fun t ht => Real.sqrt_le_sqrt (henergy t ht)); simpa using h
  have hsc0 : 0 ≤ ∫ t in (0:ℝ)..T, Real.sqrt (∫ z, (Score t z)^2 ∂P t) :=
    intervalIntegral.integral_nonneg hT (fun _ _ => Real.sqrt_nonneg _)
  have hfrac : eta^4*T^2/(2+T*Real.sqrt B)^2 ≤
      eta^4*T^2/(2+∫ t in (0:ℝ)..T, Real.sqrt (∫ z, (Score t z)^2 ∂P t))^2 := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    gcongr
  have hout := (ENNReal.ofReal_le_ofReal (sub_le_sub_right hfrac _)).trans hh
  assumption


 theorem highCompleteSource_cost_risk_uniform_above :
    ∃ Cfr eta0 ctr : ℝ, 1 ≤ Cfr ∧ CfrMin ≤ Cfr ∧ 0 < eta0 ∧ 0 < ctr ∧
      ∀ U : ExtensionDomain d, ∀ k D M q : ℕ,
      ∀ (_ : NeZero k) (_ : LinearOrder (HighWindowLabels d k)),
      ∀ hk : 4 ≤ k, ∀ hD : 3 ≤ D, ∀ hq : 1 ≤ q,
      ∀ hM : highCenterResolutionThreshold C ≤ (M : ℝ),
      ∀ lam ell N mu : ℝ, ∀ hell : 0 < ell, ∀ hellN : ell < N,
      let R := completeSourceRows C k D M q Cfr lam ell N mu
      let Ω := HighCompleteSourceHistory C k D M q Cfr lam ell N mu
      ∀ cf : ℝ, 0 ≤ cf → highWindowHolderConstant C*cf ≤ C.holderBound →
      let eta := cf*(k : ℝ)^(-C.smoothness)
      eta ≤ eta0 →
      ∀ cm : ℝ, 0 ≤ cm → cm ≤ 1/C.densityUpper →
      ∀ n : ℕ, ∀ E : ℝ, 0 ≤ E →
      8*highHistoryMassParameter d k C.densityLower C.densityUpper*(n:ℝ) ≤ cm/(M:ℝ) →
      let Bl := highRowTotalMass R.rowMass/highCenterMix C
      let c := highPathConstant (3^d) Q.ρ eta0
      let I := Real.sqrt ((3^d:ℕ)*(k:ℝ)^d*E)
      let delta := localScorePathLength c Bl I
      ∀ H : ℝ → Ω → HighWindowLabels d k → (r : ℕ) → (DesignSample d r) → ℝ,
      (∀ t ∈ Icc 0 delta, ∀ h j r, Integrable (H t h j r)
        (Measure.pi (fun _ : Fin r => volume.restrict (spatialPatchBox d)))) →
      (∀ t ∈ Icc 0 delta, ∀ h j r u, 0 ≤ H t h j r u) →
      (∀ t ∈ Icc 0 delta, ∀ h j r x, (∀ i, x i ∈ highTorusPatch j) →
        selectedRawSquareEnergy (highUnionSourceRawNumerator C R r Q.a (Q.v-eta^2*t) eta h j) x ≤
          H t h j r (highPatchProductChart j x)) →
      (∀ t ∈ Icc 0 delta, ∀ h,
        highSourceSpatialSeries d k n C.densityLower Q.c (H t h) ≤ (3^d:ℕ)*(k:ℝ)^d*E) →
      ENNReal.ofReal (ctr*eta^4/(1+Bl^2+(k:ℝ)^d*E)-
        (effectiveVarianceUpper C-C.varianceLower)^2 *
          (2*Real.exp (-(cm/(M:ℝ))^2/(8*highHistoryMassParameter d k C.densityLower C.densityUpper)))) ≤
        minimaxRisk (C.withDomain U) n := by
  obtain ⟨Cfr,eta0,hCfr,hmin,heta0,hpath⟩ := highCompleteSource_minimax_path_bound_uniform_above Q CfrMin
  let c := highPathConstant (3^d) Q.ρ eta0
  have hc  := highPathConstant_pos (3^d) Q.ρ_pos heta0
  let ctr := c^2/(3*(3^d:ℕ)*(2+c)^2)
  have hctr : 0 < ctr := by positivity
  refine ⟨Cfr,eta0,ctr,hCfr,hmin,heta0,hctr,?_⟩
  intro U k D M q hk0 horder hk hD hq hM lam ell N mu hell hellN
  letI := hk0
  letI := horder
  let R := completeSourceRows C k D M q Cfr lam ell N mu
  have G := completeSourceRows_guards k hD hq hM lam mu hCfr hell hellN
  dsimp
  intro cf hcf hcfH heta cm hcm hcmU n E hE heps H hH hH0 hdom hbudget
  let eta := cf*(k:ℝ)^(-C.smoothness)
  let Bl := highRowTotalMass R.rowMass/highCenterMix C
  let I := Real.sqrt ((3^d:ℕ)*(k:ℝ)^d*E)
  let delta := localScorePathLength c Bl I
  have hBl  := div_nonneg G.total_positive.le (highCenterMix_mem C).1.le
  have hI : 0 ≤ I := Real.sqrt_nonneg _
  have hdelt  := localScorePathLength_pos hc hBl hI
  have hnumE : 0 ≤ (k:ℝ)^d*E := mul_nonneg (by positivity) hE
  have hbudget0 : 0 ≤ (3^d:ℕ)*(k:ℝ)^d*E := by positivity
  have hsmall := highPath_update_budget (3^d) Q.ρ_pos heta0 hBl hI
  have heta0' : 0 ≤ eta := by positivity
  have hV := highPath_variance_budget (3^d) Q.ρ_pos heta0 hBl hI heta0' heta
  have hh := hpath U k D M q hk0 horder hk hD hq hM lam ell N mu hell hellN
    cf hcf hcfH heta cm hcm hcmU n delta ((3^d:ℕ)*(k:ℝ)^d*E) hdelt.le hbudget0
    hsmall hV heps H hH hH0 hdom hbudget
  have hIE : I^2 = (3^d:ℕ)*((k:ℝ)^d*E) := by
    simpa only [I,mul_assoc] using Real.sq_sqrt hbudget0
  have hK : (1:ℝ) ≤ (3^d:ℕ) := by bound
  have hn := score_cost_scaled_numeric (eta := eta) hc hBl hI (mul_nonneg hdelt.le hI)
    (show delta*I ≤ localScorePathLength c Bl I*I from le_rfl) hK hnumE hIE
  have hout := (ENNReal.ofReal_le_ofReal (sub_le_sub_right hn _)).trans hh
  exact hout


end NearlyMinimax
