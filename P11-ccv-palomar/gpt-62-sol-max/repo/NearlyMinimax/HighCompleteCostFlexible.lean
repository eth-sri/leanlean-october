module

public import NearlyMinimax.HighUnionRawFisher
public import NearlyMinimax.CompleteSourceMassAnnihilation
public import NearlyMinimax.CompleteSourceSaddleMassTail
public import NearlyMinimax.HighPriorRisk
public import NearlyMinimax.HighParameterPath
public import NearlyMinimax.HighUnionSourceUniformModel
public import NearlyMinimax.TernaryEffectiveInterval
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
attribute [local irreducible] highUnionSourceDensity highUnionSourceRegression highUnionSourceState
  historyMarkedPrior massPowerNormalizer highRawDensityMass highMarginalRealScore highRealSampleKernel

section
variable {d : ℕ}

/-- The frame and path constants are fixed before the extension domain.
A uniform local numerator envelope supplies the Fisher energy of the entire path. -/
theorem highCompleteSource_cost_risk_uniform_above [NeZero d]
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) (CfrMin : ℝ) :
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
      ∀ H : (r : ℕ) → (Fin r → Covariate d) → ℝ,
      (∀ r, Integrable (H r) (fullSpatialPatchDesign d r)) →
      (∀ r u, 0 ≤ H r u) →
      (∀ V : ℝ, |V-Q.v| ≤ Q.ρ → ∀ h : Ω, ∀ j r x,
        (∀ i, x i ∈ highTorusPatch d k j) →
        selectedRawSquareEnergy (highUnionSourceRawNumerator C R r Q.a V eta h j) x ≤
          H r (highPatchProductChart d k j x)) →
      highSourceSpatialSeries d k n C.densityLower Q.c (fun _ => H) ≤ (3^d:ℕ)*(k:ℝ)^d*E →
      ENNReal.ofReal (ctr*eta^4/(1+Bl^2+(k:ℝ)^d*E)-
        (effectiveVarianceUpper C-C.varianceLower)^2 *
          (2*Real.exp (-(cm/(M:ℝ))^2/(8*highHistoryMassParameter d k C.densityLower C.densityUpper)))) ≤
        minimaxRisk (C.withDomain U) n := by
  obtain ⟨Cfr,eta0,hCfr,hmin,heta0,hmodel⟩ := highUnionSource_original_model_uniform C Q CfrMin
  let c := highPathConstant (3^d) Q.ρ eta0
  have hc := highPathConstant_pos (3^d) Q.ρ_pos heta0
  let ctr := c^2/(3*(3^d:ℕ)*(2+c)^2)
  refine ⟨Cfr,eta0,ctr,hCfr,hmin,heta0,div_pos (sq_pos_of_pos hc) (by positivity),?_⟩
  intro U k D M q hk0 horder hk hD hq hM lam ell N mu hell hellN
  letI := hk0
  letI := horder
  let R := completeSourceRows C k D M q Cfr lam ell N mu
  let Ω := HighCompleteSourceHistory C k D M q Cfr lam ell N mu
  let Mark := SourceRowMark d D M q (C.densityLower+1/(M:ℝ)) (C.densityUpper-1/(M:ℝ)) Cfr lam ell N mu
  obtain ⟨G, hpos⟩ := completeSourceRows_guards C k D M q hD hq hM Cfr lam ell N mu hCfr hell hellN
  letI : StandardBorelSpace (HighUnionMark Mark) := highUnionMark_standardBorel
  letI := highUnionSourceLaw_probability C R G
  dsimp only
  intro cf hcf hcfH
  let eta := cf*(k : ℝ)^(-C.smoothness)
  intro heta cm hcm hcmU n E hE heps H hH hH0 hdom hbudget
  let Ba := highRowTotalMass R.rowMass/highCenterMix C
  let B := (3^d:ℕ)*(k:ℝ)^d*E
  let I := Real.sqrt B
  let T := localScorePathLength c Ba I
  have hBa := div_nonneg G.total_positive.le (highCenterMix_mem C).1.le
  have hI := Real.sqrt_nonneg B
  have hT := (localScorePathLength_pos hc hBa hI).le
  have hnumE : 0 ≤ (k:ℝ)^d*E := by positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hsmall := highPath_update_budget (3^d) Q.ρ_pos heta0 hBa hI
  have hVbudget := highPath_variance_budget (3^d) Q.ρ_pos heta0 hBa hI
    (show 0 ≤ eta by dsimp [eta]; positivity) heta
  let p := highUnionSourceDensity C R
  let F := highUnionSourceRegression C R eta
  have hp := highUnionSourceDensity_joint_measurable C R G
  have hF := highUnionSourceRegression_joint_measurable C R G eta
  let π := highUnionLaw R (highCenterMix C)
  let act := highUnionActivation R (highCenterMix C)
  let ν (t : ℝ) := historyMarkedPrior (highNeighbors d k) (3^d) t π act
  let priorBounds : HistoryPriorBounds (highNeighbors d k) (3^d) π act T Ba :=
    highUnionSource_priorBounds C R G hpos T hsmall
  have hV (t : ℝ) (ht : t ∈ Icc 0 T) : |(Q.v-eta^2*t)-Q.v| ≤ Q.ρ := by
    simp only [sub_sub_cancel_left,abs_neg,abs_mul,abs_of_nonneg (sq_nonneg eta),abs_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_left ht.2 (sq_nonneg eta)).trans hVbudget
  have hModel (t : ℝ) (ht : t ∈ Icc 0 T) (h : Ω) :=
    hmodel U k D hk0 horder hk _ inferInstance Mark inferInstance inferInstance
      R (M:ℝ) G cf hcf hcfH heta h _ (hV t ht)
  have hqFloor (t : ℝ) (ht : t ∈ Icc 0 T) (h : Ω) := (hModel t ht h).1
  have hqPos (t : ℝ) (ht : t ∈ Icc 0 T) (h : Ω) (x : Covariate d) (y : Fin 3) := Q.c_pos.trans_le (hqFloor t ht h x y)
  have hqNonneg := fun t ht h x y => (hqPos t ht h x y).le
  let θ := highNormalizedParameterPath T hT Q.a Q.v eta Q.a_pos.ne' p F hF hqNonneg
  let bad : ℝ → Set Ω := fun _ => {h | cm/(M:ℝ) < |highUnionSourceMass C R h-1|}
  let eps := 2*Real.exp (-(cm/(M:ℝ))^2/(8*highHistoryMassParameter d k C.densityLower C.densityUpper))
  have hm := highUnionSourceMass_measurable C R G
  have hbad (t : ℝ) (_ : t ∈ Icc 0 T) : MeasurableSet (bad t) :=
    measurableSet_lt measurable_const ((hm.sub_const 1).abs)
  have hlegal (t : ℝ) (ht : t ∈ Icc 0 T) (h : Ω) (hh : h ∉ bad t) :
      Admissible (C.withDomain U) (θ t h) := by
    have hgood : |highUnionSourceMass C R h-1| ≤ cm/(M:ℝ) := le_of_not_gt hh
    obtain ⟨_,hlegal⟩ := (hModel t ht h).2 cm hcm hcmU hgood
    change Admissible (C.withDomain U)
      (highNormalizedParameterPath T hT Q.a Q.v eta Q.a_pos.ne' p F hF hqNonneg t h)
    rw [highNormalizedParameterPath_apply T hT Q.a Q.v eta Q.a_pos.ne' p F hF hqNonneg t ht h]
    exact hlegal
  have hmassEq : (fun h => highRawDensityMass (p h)) = highUnionSourceMass C R := by
    funext h
    simp only [p, highRawDensityMass, highUnionSourceMass]
  have hmass (t : ℝ) (ht : t ∈ Icc 0 T) :
      Measure.map (fun h => highRawDensityMass (p h)) (ν t) =
      Measure.map (fun h => highRawDensityMass (p h)) (ν 0) := by
    have h1 := completeSourceMass_prior_law C hD hq hM Cfr lam ell N mu hCfr hell hellN T hsmall t ht
    have h0 := completeSourceMass_prior_law C hD hq hM Cfr lam ell N mu hCfr hell hellN T hsmall 0 ⟨le_rfl,hT⟩
    rw [hmassEq]
    exact h1.trans h0.symm
  have hbadmass (t : ℝ) (ht : t ∈ Icc 0 T) :
      (massPowerTilt (ν t) (fun h => highRawDensityMass (p h)) n).real (bad t) ≤ eps := by
    rw [hmassEq]
    exact completeSourceMass_prior_tilted_tail C hD hq hM Cfr lam ell N mu hCfr hell hellN
      (by omega) T hsmall n (cm/(M:ℝ)) heps t ht
  have hfisher (t : ℝ) (ht : t ∈ Icc 0 T) := by
    letI := priorBounds.probability ht
    exact highUnionSource_raw_fisher_bound C R G hpos (ν t) n hk Q.a (Q.v-eta^2*t) eta Q.c
      Q.a_pos.ne' Q.c_pos (hqFloor t ht)
      (fun j h x => completeSourceDensity_product_zero C hD hq hM Cfr lam ell N mu hCfr hell hellN j h n x)
      (fun _ _ => H) (fun _ _ => hH) (fun _ _ => hH0) (hdom _ (hV t ht)) B (fun _ => hbudget)
  have hr := historyMarkedPrior_original_minimax_path_bound priorBounds hT (C.withDomain U) n Q.a Q.v eta
    C.densityLower C.densityUpper B eps Q.a_pos C.densityLower_pos p F hp hF
    (highUnionSourceDensity_coarse_interval C R G) hqPos hmass θ
    (fun t ht h => highNormalizedParameterPath_apply T hT Q.a Q.v eta Q.a_pos.ne' p F hF hqNonneg t ht h)
    (fun t ht => Q.effective_interval (hV t ht)) bad hbad hlegal hbadmass
    hfisher

  have hK : (1 : ℝ) ≤ (3^d : ℕ) := by exact_mod_cast one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 3)
  have hn := score_cost_scaled_numeric (eta := eta) hc hBa hI (mul_nonneg hT hI)
    le_rfl hK hnumE (show I^2 = (3^d:ℕ)*((k:ℝ)^d*E) by
      simpa only [I, B, mul_assoc] using Real.sq_sqrt hB)
  exact (ENNReal.ofReal_le_ofReal (sub_le_sub_right hn _)).trans hr

end

end NearlyMinimax
