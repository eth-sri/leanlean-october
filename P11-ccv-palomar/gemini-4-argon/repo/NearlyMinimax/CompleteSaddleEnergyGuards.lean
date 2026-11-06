module
public import NearlyMinimax.HighTimeMarginal
public import NearlyMinimax.HighUnionScorePrimitives
public import NearlyMinimax.HighFrameDesignEnergy
public import NearlyMinimax.CompleteSourceMassAnnihilation
public import NearlyMinimax.PaperGoals
public import Mathlib.Analysis.SpecificLimits.Basic
public import NearlyMinimax.HigherBandActivityConversion
public import NearlyMinimax.FieldTailSummation
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal BigOperators Topology
namespace NearlyMinimax
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section
variable {d k F : ℕ}
section
section
variable {J : Type*} [Fintype J] [LinearOrder J]
def highHistoryIndexTimeKernel {E : Type*} [MeasurableSpace E] 
    (dependent : J → J → Prop) (Δ : ℕ) (π : Measure E)
    [SFinite (historyMarkedReference dependent Δ π)]
    (activation : E → ℝ) (ham : Measurable activation) (n : ℕ) (a v η : ℝ)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) :
    Kernel ℝ ((Fin n → Covariate d) × (Fin n → Fin 3)) :=
  (Kernel.const ℝ (highSampleReference d n)).withDensity
    (fun t z => ENNReal.ofReal
      (highMarginalRawLikelihood (historyMarkedPrior dependent Δ t π activation) n a (v-η^2*t) p F z /
        massPowerNormalizer (historyMarkedPrior dependent Δ t π activation)
          (fun ω => highRawDensityMass (p ω)) n))
instance highHistoryIndexTimeKernel_isSFinite {E : Type*} [MeasurableSpace E] {d : ℕ}
    (dependent : J → J → Prop) (Δ : ℕ) (π : Measure E)
    [SFinite (historyMarkedReference dependent Δ π)]
    (activation : E → ℝ) (ham : Measurable activation) (n : ℕ) (a v η : ℝ)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) :
    IsSFiniteKernel (highHistoryIndexTimeKernel dependent Δ π activation ham n a v η p F hp hF) := Kernel.isSFiniteKernel_withDensity_of_isFiniteKernel _ (fun _ _ => ENNReal.ofReal_ne_top)
def highHistoryRealTimeKernel {E : Type*} [MeasurableSpace E] 
    (dependent : J → J → Prop) (Δ : ℕ) (π : Measure E)
    [SFinite (historyMarkedReference dependent Δ π)]
    (activation : E → ℝ) (ham : Measurable activation) (n : ℕ) (a v η : ℝ)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) :
    Kernel ℝ (Fin n → Observation d) :=
  (highHistoryIndexTimeKernel dependent Δ π activation ham n a v η p F hp hF).map (encodeDesignResponse a)
instance highHistoryRealTimeKernel_isSFinite {E : Type*} [MeasurableSpace E] {d : ℕ}
    (dependent : J → J → Prop) (Δ : ℕ) (π : Measure E)
    [SFinite (historyMarkedReference dependent Δ π)]
    (activation : E → ℝ) (ham : Measurable activation) (n : ℕ) (a v η : ℝ)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) :
    IsSFiniteKernel (highHistoryRealTimeKernel dependent Δ π activation ham n a v η p F hp hF) := by
  unfold highHistoryRealTimeKernel
  infer_instance
theorem highHistoryRealTimeKernel_eq_data {E : Type*} [MeasurableSpace E] 
    (dependent : J → J → Prop) (Δ : ℕ) (π : Measure E)
    [SFinite (historyMarkedReference dependent Δ π)]
    (activation : E → ℝ) (ham : Measurable activation) (n : ℕ) (a v η : ℝ)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (t : ℝ) [IsProbabilityMeasure (historyMarkedPrior dependent Δ t π activation)]
    (aRaw bRaw : ℝ) (haRaw : 0 < aRaw) (ha : a ≠ 0)
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) (v-η^2*t) y) :
    highHistoryRealTimeKernel dependent Δ π activation ham n a v η p F hp hF t =
      (highRealSampleKernel n a (v-η^2*t) p F hp hF) ∘ₘ
        massPowerTilt (historyMarkedPrior dependent Δ t π activation)
          (fun ω => highRawDensityMass (p ω)) n := by
  have h_highHistoryIndexTimeKernel_apply : highHistoryIndexTimeKernel dependent Δ π activation ham n a v η p F hp hF t =
      (highSampleReference d n).withDensity (fun z => ENNReal.ofReal
        (highMarginalRawLikelihood (historyMarkedPrior dependent Δ t π activation)
          n a (v-η^2*t) p F z /
          massPowerNormalizer (historyMarkedPrior dependent Δ t π activation)
            (fun ω => highRawDensityMass (p ω)) n)) := by
    have hd  :=
      ((highMarginalRawLikelihood_time_measurable dependent Δ π activation ham n a v η p F hp hF).div
        ((highMassPowerNormalizer_time_measurable dependent Δ π activation ham n p hp).comp measurable_fst)).ennreal_ofReal
    exact Kernel.withDensity_apply _ hd t
  rw [highHistoryRealTimeKernel, Kernel.map_apply _ (encodeDesignResponse_measurable a),
    h_highHistoryIndexTimeKernel_apply, ← highMassTilt_index_marginal_density
      (historyMarkedPrior dependent Δ t π activation) n a (v-η^2*t) p F hp hF aRaw bRaw haRaw ha hraw hq,
    Measure.map_comp _ _ (encodeDesignResponse_measurable a)]
  rfl
theorem highHistoryScore_sqrt_energy_intervalIntegrable {E : Type*} [MeasurableSpace E]
    [StandardBorelSpace E] 
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (π : Measure E) [IsProbabilityMeasure π]
    [SFinite (historyMarkedReference dependent Δ π)]
    (activation : E → ℝ) (ham : Measurable activation)
    (Ba : ℝ) (hBa : 0 ≤ Ba) (habound : ∀ e, |activation e| ≤ Ba)
    (n : ℕ) (a v η aRaw bRaw T M : ℝ) (ha : 0 < a) (haRaw : 0 < aRaw) (hT : 0 ≤ T)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (hprob : ∀ t ∈ Icc 0 T, IsProbabilityMeasure (historyMarkedPrior dependent Δ t π activation))
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ t ∈ Icc 0 T, ∀ ω x y, 0 < ternaryMass a (F ω x) (v-η^2*t) y)
    (hE : ∀ t ∈ Icc 0 T, Integrable
      (fun z : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
        (highHistoryLikelihoodDerivative dependent hsymm π activation n a (v-η^2*t) η p F z.1 z.2)^2 /
          highRawSampleLikelihood n a (v-η^2*t) (p z.1) (F z.1) z.2)
      ((historyMarkedPrior dependent Δ t π activation).prod (highSampleReference d n)))
    (hbudget : ∀ t ∈ Icc 0 T,
      (massPowerNormalizer (historyMarkedPrior dependent Δ t π activation)
        (fun ω => highRawDensityMass (p ω)) n)⁻¹ *
        ∫ z : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)),
          (highHistoryLikelihoodDerivative dependent hsymm π activation n a (v-η^2*t) η p F z.1 z.2)^2 /
            highRawSampleLikelihood n a (v-η^2*t) (p z.1) (F z.1) z.2
          ∂(historyMarkedPrior dependent Δ t π activation).prod (highSampleReference d n) ≤ M) :
    IntervalIntegrable (fun t => Real.sqrt (∫ z,
      (highMarginalRealScore dependent hsymm (historyMarkedPrior dependent Δ t π activation)
        π activation n a (v-η^2*t) η p F z)^2
      ∂(highRealSampleKernel n a (v-η^2*t) p F hp hF) ∘ₘ
        massPowerTilt (historyMarkedPrior dependent Δ t π activation)
          (fun ω => highRawDensityMass (p ω)) n)) volume 0 T := by
  have hb (t : ℝ) (ht : t ∈ Icc 0 T) :
      (∫ z, (highMarginalRealScore dependent hsymm (historyMarkedPrior dependent Δ t π activation)
        π activation n a (v-η^2*t) η p F z)^2
        ∂highHistoryRealTimeKernel dependent Δ π activation ham n a v η p F hp hF t) ≤ M := by
    letI := hprob t ht
    rw [highHistoryRealTimeKernel_eq_data dependent Δ π activation ham n a v η p F hp hF
      t aRaw bRaw haRaw ha.ne' hraw (fun ω x y => (hq t ht ω x y).le)]
    exact (highMarginalRealScore_memLp_energy dependent hsymm
      (historyMarkedPrior dependent Δ t π activation) π activation ham Ba hBa habound
      n a (v-η^2*t) η aRaw bRaw ha haRaw p F hp hF hraw (hq t ht) (hE t ht)).2.trans
      (hbudget t ht)
  have h_highMarginalRealScore_time_measurable : Measurable (fun z : ℝ × (Fin n → Observation d) =>
      highMarginalRealScore dependent hsymm (historyMarkedPrior dependent Δ z.1 π activation)
        π activation n a (v-η^2*z.1) η p F z.2) := by
    change Measurable ((fun z : ℝ × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
      highMarginalIndexScore dependent hsymm (historyMarkedPrior dependent Δ z.1 π activation)
        π activation n a (v-η^2*z.1) η p F z.2) ∘
      (fun z : ℝ × (Fin n → Observation d) => (z.1, decodeDesignResponse a z.2)))
    exact (highMarginalIndexScore_time_measurable dependent hsymm Δ π activation ham n a v η p F hp hF).comp
      (show Measurable (fun z : ℝ × (Fin n → Observation d) =>
        (z.1, decodeDesignResponse a z.2)) from
        measurable_fst.prodMk ((decodeDesignResponse_measurable a).comp measurable_snd))
  have h_highHistoryScoreEnergyProxy_measurable  := ((h_highMarginalRealScore_time_measurable.pow_const 2).stronglyMeasurable.integral_kernel_prod_right'
    (κ := highHistoryRealTimeKernel dependent Δ π activation ham n a v η p F hp hF)).measurable
  have h_intervalIntegrable_sqrt_of_measurable_bound (f : ℝ → ℝ) (hf : Measurable f) (hbound : ∀ t ∈ Icc 0 T, f t ≤ M) : IntervalIntegrable (fun t => Real.sqrt (f t)) volume 0 T := by
    apply (intervalIntegrable_const (c := Real.sqrt M)).mono_fun'
      (Real.continuous_sqrt.measurable.comp hf).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    rw [uIoc_of_le hT] at ht
    dsimp only [Function.comp_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt (hbound t ⟨ht.1.le, ht.2⟩)
  apply (h_intervalIntegrable_sqrt_of_measurable_bound _ h_highHistoryScoreEnergyProxy_measurable hb).congr
  intro t ht
  rw [uIoc_of_le hT] at ht
  letI := hprob t ⟨ht.1.le,ht.2⟩
  dsimp only
  rw [highHistoryRealTimeKernel_eq_data dependent Δ π activation ham n a v η p F hp hF
    t aRaw bRaw haRaw ha.ne' hraw (fun ω x y => (hq t ⟨ht.1.le,ht.2⟩ ω x y).le)]
end
variable {J : Type*} [Fintype J] [LinearOrder J]
attribute [local irreducible] highMarginalRealScore highRealSampleKernel historyMarkedPrior
  massPowerTilt massPowerNormalizer highRawDensityMass
theorem historyMarkedPrior_original_minimax_path_bound
    (dependent : J → J → Prop) (hrefl : ∀ j, dependent j j)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    {E : Type*} [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (activation : E → ℝ)
    (ham : Measurable activation) (hact : ∫ e, activation e ∂π = 0)
    (Ba T : ℝ) (hBa : 0 ≤ Ba) (hT : 0 ≤ T) (hab : ∀ e, |activation e| ≤ Ba)
    (hsmall : T * Ba / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ)^2))
     (C : ModelConstants d) (n : ℕ) (a v η aRaw bRaw M ε : ℝ)
    (ha : 0 < a) (haRaw : 0 < aRaw)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ t ∈ Icc 0 T, ∀ ω x y, 0 < ternaryMass a (F ω x) (v-η^2*t) y)
    (hmass : ∀ t ∈ Icc 0 T,
      (historyMarkedPrior dependent Δ t π activation).map (fun ω => highRawDensityMass (p ω)) =
      (historyMarkedPrior dependent Δ 0 π activation).map (fun ω => highRawDensityMass (p ω)))
    (θ : ℝ → HistoryMarked dependent E → RegressionParameter d)
    (hθ : ∀ (t : ℝ) (ht : t ∈ Icc 0 T), ∀ ω, θ t ω =
      normalizedDensityTernaryParameter (p ω) (F ω) a (v-η^2*t) hF.of_uncurry_left
        ha.ne' (fun x y => (hq t ht ω x y).le))
    (hV : ∀ t ∈ Icc 0 T, v-η^2*t ∈ Icc C.varianceLower (effectiveVarianceUpper C))
    (bad : ℝ → Set (HistoryMarked dependent E))
    (hbad : ∀ t ∈ Icc 0 T, MeasurableSet (bad t))
    (hlegal : ∀ t ∈ Icc 0 T, ∀ ω ∉ bad t, Admissible C (θ t ω))
    (hbadmass : ∀ t ∈ Icc 0 T,
      (massPowerTilt (historyMarkedPrior dependent Δ t π activation)
        (fun ω => highRawDensityMass (p ω)) n).real (bad t) ≤ ε)
    (hE : ∀ t ∈ Icc 0 T, Integrable
      (fun z : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
        (highHistoryLikelihoodDerivative dependent hsymm π activation n a (v-η^2*t) η p F z.1 z.2)^2 /
          highRawSampleLikelihood n a (v-η^2*t) (p z.1) (F z.1) z.2)
      ((historyMarkedPrior dependent Δ t π activation).prod (highSampleReference d n)))
    (hbudget : ∀ t ∈ Icc 0 T,
      (massPowerNormalizer (historyMarkedPrior dependent Δ t π activation)
        (fun ω => highRawDensityMass (p ω)) n)⁻¹ *
        ∫ z : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)),
          (highHistoryLikelihoodDerivative dependent hsymm π activation n a (v-η^2*t) η p F z.1 z.2)^2 /
            highRawSampleLikelihood n a (v-η^2*t) (p z.1) (F z.1) z.2
          ∂(historyMarkedPrior dependent Δ t π activation).prod (highSampleReference d n) ≤ M) :
    let P (t : ℝ) := (highRealSampleKernel n a (v-η^2*t) p F hp hF) ∘ₘ
      massPowerTilt (historyMarkedPrior dependent Δ t π activation)
        (fun ω => highRawDensityMass (p ω)) n
    let R (t : ℝ) := highMarginalRealScore dependent hsymm
      (historyMarkedPrior dependent Δ t π activation) π activation n a (v-η^2*t) η p F
    ENNReal.ofReal (η^4*T^2 /
      (2 + ∫ t in ↑0..T, Real.sqrt (∫ z, (R t z)^2 ∂P t))^2 -
      (effectiveVarianceUpper C-C.varianceLower)^2*ε) ≤ minimaxRisk C n := by
  let ν (t : ℝ) := historyMarkedPrior dependent Δ t π activation
  let σ (t : ℝ) := massPowerTilt (ν t) (fun ω => highRawDensityMass (p ω)) n
  let L (t : ℝ) := highRealSampleKernel n a (v-η^2*t) p F hp hF
  let R (t : ℝ) := highMarginalRealScore dependent hsymm (ν t) π activation n a (v-η^2*t) η p F
  let _ := historyMarkedReference_probability dependent hrefl hsymm Δ hΔ hlabels π
  have hai : Integrable activation π := Integrable.of_bound ham.aestronglyMeasurable Ba
    (Eventually.of_forall fun e => by simpa only [Real.norm_eq_abs] using hab e)
  have hν (t : ℝ) (ht : t ∈ Icc 0 T) : IsProbabilityMeasure (ν t) := by
    have hs : t*Ba/historyReferenceRho Δ ≤ 1/(2+8*(Δ:ℝ)^2) :=
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ht.2 hBa)
        (historyReferenceRho_pos Δ).le).trans hsmall
    exact historyMarkedPrior_probability dependent hrefl hsymm Δ hΔ hlabels t Ba ht.1 hBa
      π activation hai hact hab hs
  have hσ (t : ℝ) (ht : t ∈ Icc 0 T) : IsProbabilityMeasure (σ t) := by
    let _ := hν t ht
    exact massPowerTilt_isProbability (ν t) _ (highRawDensityMass_joint_measurable p hp)
      n aRaw bRaw haRaw (fun ω => highRawDensityMass_mem_Icc (p ω) hp.of_uncurry_left
        aRaw bRaw haRaw (Eventually.of_forall (hraw ω)))
  have hL (t : ℝ) (ht : t ∈ Icc 0 T) : IsMarkovKernel (L t) :=
    highRealSampleKernel_markov n a (v-η^2*t) p F hp hF aRaw bRaw haRaw hraw ha.ne'
      (fun ω x y => (hq t ht ω x y).le)
  have hsample (t : ℝ) (ht : t ∈ Icc 0 T) (ω) : L t ω = sampleLaw (θ t ω) n := by
    rw [hθ t ht ω]
    exact highRealSampleKernel_eq_sampleLaw n a (v-η^2*t) p F hp hF aRaw bRaw haRaw hraw
      ha.ne' (fun ω x y => (hq t ht ω x y).le) ω
  have hvariance (t : ℝ) (ht : t ∈ Icc 0 T) (ω) : (θ t ω).variance = v-η^2*t := by
    rw [hθ t ht ω]
    rfl
  have hR : ∀ᵐ t ∂volume, t ∈ Icc 0 T → MemLp (R t) 2 (L t ∘ₘ σ t) :=
    Eventually.of_forall fun t ht => by
      let _ := hν t ht
      exact (highMarginalRealScore_memLp_energy dependent hsymm (ν t) π activation ham
        Ba hBa hab n a (v-η^2*t) η aRaw bRaw ha haRaw p F hp hF hraw (hq t ht) (hE t ht)).1
  have hc := historyMarkedPrior_dataScore_centered_ae dependent hrefl hsymm Δ hΔ hlabels
    T Ba hBa π activation ham hact hab hsmall n a v η aRaw bRaw ha haRaw p F hp hF hraw hq hmass
  have hB : 0 ≤ effectiveVarianceUpper C :=
    C.varianceLower_pos.le.trans (effective_variance_interval_nondegenerate C).le
  have hAC (S : BoundedEstimator C n) : AbsolutelyContinuousOnInterval
      (fun t => ∫ z, S.val.val z ∂(L t ∘ₘ σ t)) 0 T :=
    historyMarkedPrior_dataMean_absolutelyContinuous dependent hrefl hsymm Δ hΔ hlabels
      T Ba hBa π activation ham hact hab hsmall n a v η aRaw bRaw ha haRaw p F hp hF hraw
      (fun t ht ω x y => (hq t ht ω x y).le) hmass S.val.val S.val.property
      (effectiveVarianceUpper C) hB (fun z => by
        rw [abs_of_nonneg (C.varianceLower_pos.le.trans (S.property z).1)]
        exact (S.property z).2) hT
  have hd (S : BoundedEstimator C n) :=
    historyMarkedPrior_dataMean_score_hasDerivAt_ae dependent hrefl hsymm Δ hΔ hlabels
      T Ba hBa π activation ham hact hab hsmall n a v η aRaw bRaw ha haRaw p F hp hF hraw hq hmass
      S.val.val S.val.property (effectiveVarianceUpper C) hB (fun z => by
        rw [abs_of_nonneg (C.varianceLower_pos.le.trans (S.property z).1)]
        exact (S.property z).2)
  have hi := highHistoryScore_sqrt_energy_intervalIntegrable dependent hsymm Δ π activation ham
    Ba hBa hab n a v η aRaw bRaw T M ha haRaw hT p F hp hF hν hraw hq hE hbudget
  have hh := paper_score_to_risk C σ L θ (fun t => v-η^2*t) R T ε hT hσ hL hsample hvariance
    hV bad hbad hlegal hbadmass hR hc hAC hd hi
  have he : ((v-η^2*T)-(v-η^2*0))^2 = η^4*T^2 := by ring
  dsimp only at hh ⊢
  rw [he] at hh
  exact hh
end
section
section
attribute [local irreducible] highUnionSourceDensity highUnionSourceState historyMarkedAppend
  highUnionSourceRegression highHistoryLikelihoodScore highSampleIndexKernel
variable {d k D : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
    [∀ i, MeasurableSpace (E i)] [∀ i, StandardBorelSpace (E i)]
    [NeZero k] [LinearOrder (HighWindowLabels d k)]
    (C : ModelConstants d) (R : HighUnionRowData d k D I E)
    {M Cfr : ℝ} (G : HighUnionSourceGuards C M Cfr R)
    (hpos : ∀ i, 0 < R.rowMass i)
def highUnionSourceRawNumerator (r ) (a V η : ℝ)
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E))
    (j : HighWindowLabels d k) (x : Fin r → Covariate d) (y : Fin r → Fin 3) : ℝ :=
  highMarkedSampleNumerator r (highUnionLaw R (highCenterMix C))
    (highUnionActivation R (highCenterMix C)) a V η (highUnionSourceDensity C R h)
    (highUnionSourceResetDensity C R j h) (highUnionSourceResetCoefficient C R j h)
    (highLocalFieldWithout d k D η (highUnionSourceState C R h).2 j)
    (highPeriodicTensor d k j) (fun x => highLocalFrameFeature k j x)
    ((highUnionSourceState C R h).2 j) x y
include G hpos in
theorem highUnionSource_sample_fisher_bound (n ) (hk : 4 ≤ k)
    (a V η cMass ) (ha : a ≠ 0) (hcMass : 0 < cMass)
    (hq : ∀ h x y, cMass ≤ ternaryMass a (highUnionSourceRegression C R η h x) V y)
    (hDensity : ∀ j h (x : Fin n → Covariate d),
      (∫ e, highUnionActivation R (highCenterMix C) e *
        ∏ i, highUnionSourceResetDensity C R j h e (x i) ∂highUnionLaw R (highCenterMix C)) = 0)
    (h )
    (H : HighWindowLabels d k → (r : ℕ) → (Fin r → Covariate d) → ℝ)
    (hH : ∀ j r, Integrable (H j r) (Measure.pi (fun _ : Fin r => volume.restrict (spatialPatchBox d))))
    (hH0 : ∀ j r u, 0 ≤ H j r u)
    (hdom : ∀ j r x, (∀ i, x i ∈ highTorusPatch d k j) →
      selectedRawSquareEnergy (highUnionSourceRawNumerator C R r a V η h j) x ≤
        H j r (highPatchProductChart d k j x)) :
    let hp := highUnionSourceDensity_joint_measurable C R G
    let hF := highUnionSourceRegression_joint_measurable C R G η
    let S := highHistoryLikelihoodScore (fun i j => j ∈ highNeighborLabels d k i)
      (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h)
      (highUnionLaw R (highCenterMix C)) (highUnionActivation R (highCenterMix C))
      n a V η (highUnionSourceDensity C R) (highUnionSourceRegression C R η) h
    Integrable (fun z => S z ^ 2)
      (highSampleIndexKernel n a V (highUnionSourceDensity C R) (highUnionSourceRegression C R η) hp hF h) ∧
    (∫ z, S z ^ 2 ∂highSampleIndexKernel n a V
      (highUnionSourceDensity C R) (highUnionSourceRegression C R η) hp hF h) ≤
      (3 ^ d : ℕ) * ∑ j : HighWindowLabels d k, ∑ r ∈ Finset.range (n + 1),
        (↑n * highFixedScoreDenominator C.densityLower cMass * (2 / ↑k) ^ d) ^ r /
          ↑r.factorial * ∫ u, H j r u
            ∂Measure.pi (fun _ : Fin r => volume.restrict (spatialPatchBox d)) := by
  letI : StandardBorelSpace (HighUnionMark E) := highUnionMark_standardBorel
  letI := highUnionSourceLaw_probability C R G
  let π := highUnionLaw R (highCenterMix C)
  let act := highUnionActivation R (highCenterMix C)
  let p := highUnionSourceDensity C R
  let F := highUnionSourceRegression C R η
  have hp  := highUnionSourceDensity_joint_measurable C R G
  have hF  := highUnionSourceRegression_joint_measurable C R G η
  have ham := highUnionActivation_measurable R G.activation_measurable (highCenterMix C)
  have hai : Integrable act π := Integrable.of_bound ham.aestronglyMeasurable
    (highRowTotalMass R.rowMass / highCenterMix C)
    (Filter.Eventually.of_forall (fun e => by simpa only [Real.norm_eq_abs] using (highUnionSourceActivation_bound C R G hpos e)))
  let c := (highUnionSourceState C R h).2
  let Fh := highFrameField d k η (fun l => highFramePolynomial (c l))
  have hFh_eq : F h = Fh := by
    simp only [F,Fh,c]
    funext x
    unfold highUnionSourceRegression
    rfl
  have hreg (j : HighWindowLabels d k) (e : HighUnionMark E) (x : Covariate d) (y : Fin 3) :
      highMarkedResponseMass a V η (highLocalFieldWithout d k D η c j)
        (highPeriodicTensor d k j) (fun x => highLocalFrameFeature k j x)
        (highUnionSourceResetCoefficient C R j h e) x y =
      ternaryMass a (F (historyMarkedAppend
        (fun i j => j ∈ highNeighborLabels d k i)
        (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j (h,e)) x) V y := by
    have hr := congrFun (highUnionSourceRegression_append C R 1 hk η j h e (fun _ => x)) 0
    exact congrArg (fun t : ℝ => ternaryMass a t V y) hr
  have hs := high_frame_complete_design_spatial_series d k D n hk
    (fun _ => π) (fun _ => act) (fun _ => ham) (fun _ => hai)
    a V η C.densityLower C.densityUpper cMass ha C.densityLower_pos
    (by linarith [C.one_lt_densityUpper]) hcMass (p h) hp.of_uncurry_left
    (highUnionSourceDensity_coarse_interval C R G h)
    (fun j => highUnionSourceResetDensity C R j h)
    (fun j => highUnionSourceResetDensity_measurable C R G j h)
    (fun j => highUnionSourceResetDensity_abs_le C R G j h)
    (fun j => highUnionSourceResetDensity_outside C R j h)
    (fun j => highUnionSourceResetCoefficient C R j h)
    (fun j => highUnionSourceResetCoefficient_measurable C R G j h) c
    (by
      change ∀ x y, cMass ≤ ternaryMass a (Fh x) V y
      intro x y
      rw [← hFh_eq]
      exact hq h x y) (by
      intro j e x y
      rw [hreg]
      exact hcMass.le.trans (hq _ x y)) (fun j x => hDensity j h x) H hH hH0 hdom
  have he : highSampleIndexKernel n a V p F hp hF h =
      (Measure.pi (fun _ : Fin n => highNormalizedDesignLaw (p h))).compProd
        (responseSampleIndexKernel n a V Fh ((highFrameField_contDiff d k η _).continuous.measurable)) := by
    have hd := high_normalized_design_probability (p h) hp.of_uncurry_left
      C.densityLower C.densityUpper C.densityLower_pos
      (Filter.Eventually.of_forall (highUnionSourceDensity_coarse_interval C R G h))
    have hm  := C.densityLower_pos.trans_le
      (highRawDensityMass_mem_Icc (p h) hp.of_uncurry_left
        C.densityLower C.densityUpper C.densityLower_pos
        (Filter.Eventually.of_forall (highUnionSourceDensity_coarse_interval C R G h))).1
    rw [highSampleIndexKernel_apply]
    have hed := (highSample_index_density n (p h) (F h) hp.of_uncurry_left hF.of_uncurry_left a V hd
      (fun x => C.densityLower_pos.le.trans (highUnionSourceDensity_coarse_interval C R G h x).1)
      hm (fun x y => hcMass.le.trans (hq h x y))).symm
    simpa only [hFh_eq,highSampleReference,highNormalizedDesignLaw] using hed
  have hS : highHistoryLikelihoodScore (fun i j => j ∈ highNeighborLabels d k i)
      (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) π act n a V η p F h =
      highFrameFullMarkedScore d k D n (fun _ => π) (fun _ => act) a V η (p h)
        (fun j => highUnionSourceResetDensity C R j h)
        (fun j => highUnionSourceResetCoefficient C R j h) c := by
    funext z
    obtain ⟨x,y⟩ := z
    exact highUnionSourceLikelihoodScore_eq_sum C R n hk a V η h x y
  dsimp only
  rw [hS,he]
  exact hs
end
attribute [local irreducible] highUnionSourceDensity highUnionSourceRegression highUnionSourceState
  historyMarkedAppend highRawSampleLikelihood massPowerNormalizer
def highSourceSpatialSeries (d k n : ℕ) [NeZero k] (pMinus cMass : ℝ)
    (H : HighWindowLabels d k → (r : ℕ) → (Fin r → Covariate d) → ℝ) : ℝ :=
  (3^d : ℕ)*∑ j : HighWindowLabels d k, ∑ r ∈ Finset.range (n+1),
    (↑n*highFixedScoreDenominator pMinus cMass*(2/↑k)^d)^r /
      ↑r.factorial*∫ u, H j r u
        ∂Measure.pi (fun _ : Fin r => volume.restrict (spatialPatchBox d))
variable {d k D : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
    [∀ i, MeasurableSpace (E i)] [∀ i, StandardBorelSpace (E i)]
    [NeZero k] [LinearOrder (HighWindowLabels d k)]
    (C : ModelConstants d) (R : HighUnionRowData d k D I E)
    {M Cfr : ℝ} (G : HighUnionSourceGuards C M Cfr R)
    (hpos : ∀ i, 0 < R.rowMass i)
include G hpos in
 theorem highUnionSource_raw_fisher_bound
    (ν : Measure (HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E)))
    [IsProbabilityMeasure ν] (n : ℕ) (hk : 4 ≤ k)
    (a V η cMass : ℝ) (ha : a ≠ 0) (hcMass : 0 < cMass)
    (hq : ∀ h x y, cMass ≤ ternaryMass a (highUnionSourceRegression C R η h x) V y)
    (hDensity : ∀ j h (x : Fin n → Covariate d),
      (∫ e, highUnionActivation R (highCenterMix C) e *
        ∏ i, highUnionSourceResetDensity C R j h e (x i) ∂highUnionLaw R (highCenterMix C)) = 0)
    (H : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E) →
      HighWindowLabels d k → (r : ℕ) → (Fin r → Covariate d) → ℝ)
    (hH : ∀ h j r, Integrable (H h j r)
      (Measure.pi (fun _ : Fin r => volume.restrict (spatialPatchBox d))))
    (hH0 : ∀ h j r u, 0 ≤ H h j r u)
    (hdom : ∀ h j r x, (∀ i, x i ∈ highTorusPatch d k j) →
      selectedRawSquareEnergy (highUnionSourceRawNumerator C R r a V η h j) x ≤
        H h j r (highPatchProductChart d k j x))
    (B : ℝ) (hB : 0 ≤ B)
    (hbudget : ∀ h, highSourceSpatialSeries d k n C.densityLower cMass (H h) ≤ B) :
    let D := highHistoryLikelihoodDerivative (fun i j => j ∈ highNeighborLabels d k i)
      (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h)
      (highUnionLaw R (highCenterMix C)) (highUnionActivation R (highCenterMix C))
      n a V η (highUnionSourceDensity C R) (highUnionSourceRegression C R η)
    let L := fun h => highRawSampleLikelihood n a V
      (highUnionSourceDensity C R h) (highUnionSourceRegression C R η h)
    Integrable (fun z => D z.1 z.2 ^ 2 / L z.1 z.2) (ν.prod (highSampleReference d n)) ∧
    (massPowerNormalizer ν (fun h => highRawDensityMass (highUnionSourceDensity C R h)) n)⁻¹ *
      (∫ z, D z.1 z.2 ^ 2 / L z.1 z.2 ∂ν.prod (highSampleReference d n)) ≤ B := by
  letI : StandardBorelSpace (HighUnionMark E) := highUnionMark_standardBorel
  letI := highUnionSourceLaw_probability C R G
  let p := highUnionSourceDensity C R
  let F := highUnionSourceRegression C R η
  have hp  := highUnionSourceDensity_joint_measurable C R G
  have hF  := highUnionSourceRegression_joint_measurable C R G η
  let D := highHistoryLikelihoodDerivative (fun i j => j ∈ highNeighborLabels d k i)
    (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h)
    (highUnionLaw R (highCenterMix C)) (highUnionActivation R (highCenterMix C)) n a V η p F
  have hDm  := highHistoryLikelihoodDerivative_measurable
    (fun i j => j ∈ highNeighborLabels d k i)
    (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h)
    (highUnionLaw R (highCenterMix C)) (highUnionActivation R (highCenterMix C))
    (highUnionActivation_measurable R G.activation_measurable _) n a V η p F hp hF
  have hs (h) := highUnionSource_sample_fisher_bound C R G hpos n hk a V η cMass ha hcMass
    hq hDensity h (H h) (hH h) (hH0 h) (hdom h)
  have hj := high_raw_joint_fisher_integrable_bound ν n a V p F hp hF
    C.densityLower C.densityUpper C.densityLower_pos
    (highUnionSourceDensity_coarse_interval C R G) (fun h x y => hcMass.trans_le (hq h x y))
    D hDm B hB
    (fun h => by simpa only [highHistoryLikelihoodScore] using (hs h).1)
    (fun h => by
      have hb0 := hbudget h
      have hb := (hs h).2.trans hb0
      simpa only [highHistoryLikelihoodScore] using hb)
  have hG  :=
    massPowerNormalizer_pos ν _ (highRawDensityMass_joint_measurable p hp) n
      C.densityLower C.densityUpper C.densityLower_pos
      (fun h => highRawDensityMass_mem_Icc (p h) hp.of_uncurry_left
        C.densityLower C.densityUpper C.densityLower_pos
        (Filter.Eventually.of_forall (highUnionSourceDensity_coarse_interval C R G h)))
  refine ⟨hj.1, ?_⟩
  calc
    _ ≤ (massPowerNormalizer ν (fun h => highRawDensityMass (p h)) n)⁻¹ *
        (massPowerNormalizer ν (fun h => highRawDensityMass (p h)) n * B) :=
      mul_le_mul_of_nonneg_left hj.2 (inv_nonneg.mpr hG.le)
    _ = B := by rw [← mul_assoc, inv_mul_cancel₀ hG.ne', one_mul]
end
section Generic
variable {d k F : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
    [∀ i, MeasurableSpace (E i)] [∀ i, StandardBorelSpace (E i)]
    [NeZero k] [LinearOrder (HighWindowLabels d k)]
    (C : ModelConstants d) (R : HighUnionRowData d k F I E)
    {M Cfr : ℝ} (G : HighUnionSourceGuards C M Cfr R)
include G
theorem highUnionSourceMass_reference_tilted_tail (hk : 2 ≤ k) (n : ℕ) (ε : ℝ)
    (hε : 8*highHistoryMassParameter d k C.densityLower C.densityUpper*(n:ℝ) ≤ ε) :
    (massPowerTilt
      (historyMarkedReference (fun i j => j ∈ highNeighborLabels d k i) (3^d)
        (highUnionLaw R (highCenterMix C))) (highUnionSourceMass C R) n).real
      {h | ε < |highUnionSourceMass C R h-1|} ≤
      2*Real.exp (-ε^2/(8*highHistoryMassParameter d k C.densityLower C.densityUpper)) := by
  letI := highUnionSourceLaw_probability C R G
  letI := historyMarkedReference_probability _ (highNeighborLabels_self_mem d k)
    (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) (3^d)
    (one_le_pow₀ (by norm_num : 1 ≤ 3)) (highNeighbor_dependency_card d k)
    (highUnionLaw R (highCenterMix C))
  have h_highUnionSourceMass_reference_mean_one : (∫ h, highUnionSourceMass C R h
      ∂historyMarkedReference (fun i j => j ∈ highNeighborLabels d k i) (3^d)
        (highUnionLaw R (highCenterMix C))) = 1 := by
    letI := highUnionSourceLaw_probability C R G
    apply historyMarkedReference_mean_one (fun i j => j ∈ highNeighborLabels d k i)
      (highNeighborLabels_self_mem d k) (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h)
      (3^d) (one_le_pow₀ (by norm_num : 1 ≤ 3)) (highNeighbor_dependency_card d k)
      (highUnionLaw R (highCenterMix C)) (highUnionSourceMass C R)
      (highUnionSourceMass_measurable C R G) C.densityUpper _
      (highUnionSourceMass_fiber_mean_one C R G)
    intro h
    have hp := highUnionSourceMass_interval C R G h
    have hM0 : 0 < M := by
      have := (highCenterResolution_guards C M G.resolution).1
      linarith
    rw [abs_of_nonneg (by linarith [hp.1, C.densityLower_pos, one_div_pos.mpr hM0])]
    linarith [hp.2, one_div_pos.mpr hM0]
  have h_highUnionSourceMass_reference_mgf u : (∫ h, Real.exp (u * (highUnionSourceMass C R h-1))
      ∂historyMarkedReference (fun i j => j ∈ highNeighborLabels d k i) (3^d)
        (highUnionLaw R (highCenterMix C))) ≤
      Real.exp (highHistoryMassParameter d k C.densityLower C.densityUpper * u^2) := by
    letI := highUnionSourceLaw_probability C R G
    have hm := highUnionSourceMass_measurable C R G
    have hBound : ∀ h, |highUnionSourceMass C R h| ≤ C.densityUpper := by
      intro h
      have hp := highUnionSourceMass_interval C R G h
      have hM0 : 0 < M := by
        have := (highCenterResolution_guards C M G.resolution).1
        linarith
      rw [abs_of_nonneg (by linarith [hp.1, C.densityLower_pos, one_div_pos.mpr hM0])]
      linarith [hp.2, one_div_pos.mpr hM0]
    have : 0 ≤ C.densityUpper-C.densityLower := by
      linarith [C.densityLower_lt_one, C.one_lt_densityUpper]
    have h := historyMarkedReference_mass_mgf (fun i j => j ∈ highNeighborLabels d k i)
      (highNeighborLabels_self_mem d k) (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h)
      (3^d) (one_le_pow₀ (by norm_num : ↑1 ≤ 3)) (highNeighbor_dependency_card d k)
      (highUnionLaw R (highCenterMix C)) (highUnionSourceMass C R) hm C.densityUpper
      ((2 / ↑k)^d * (C.densityUpper-C.densityLower)) (by positivity)
      hBound (highUnionSourceMass_fiber_mean_one C R G)
      (fun g j marks marks' hMarks => highUnionSourceMass_block_oscillation C R G hk g marks marks' j hMarks) u
    convert h using 1
    congr 1
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin, Nat.cast_pow]
    unfold highHistoryMassParameter
    ring
  have h_highUnionSourceMass_coarse_interval (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E)) : highUnionSourceMass C R h ∈ Icc C.densityLower C.densityUpper := by
    have hM0 : 0 < M := by linarith [(highCenterResolution_guards C M G.resolution).1]
    have hb := highUnionSourceMass_interval C R G h
    constructor
    · exact (le_add_of_nonneg_right (one_div_pos.mpr hM0).le).trans hb.1
    · exact hb.2.trans (sub_le_self _ (one_div_pos.mpr hM0).le)
  have h_highHistoryMassParameter_pos (a) (b) (hk : 0 < k) (hab : a < b) : 0 < highHistoryMassParameter d k a b := by
    unfold highHistoryMassParameter
    positivity
  exact massPowerTilt_abs_tail _ _ (highUnionSourceMass_measurable C R G) n
    C.densityLower C.densityUpper C.densityLower_pos h_highUnionSourceMass_coarse_interval
    h_highUnionSourceMass_reference_mean_one _ ε
    (h_highHistoryMassParameter_pos _ _ (by omega) (C.densityLower_lt_one.trans C.one_lt_densityUpper))
    h_highUnionSourceMass_reference_mgf hε
end Generic
section ActualFinePair
variable {d k D M q : ℕ} [NeZero d] [NeZero k] [LinearOrder (HighWindowLabels d k)]
    (C : ModelConstants d) (Cfr T₀ N : ℝ)
    (hD : 3 ≤ D) (hq : 1 ≤ q) (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
    (hCfr : 1 ≤ Cfr) (hT₀ : 0 < T₀) (hTN : T₀ < N)
include hD hq hM hCfr hT₀ hTN
end ActualFinePair
section
variable {d k D M q : ℕ} [NeZero d] [NeZero k] [LinearOrder (HighWindowLabels d k)]
    (C : ModelConstants d) (hD : 3 ≤ D) (hq : 1 ≤ q)
    (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
    (Cfr lam ℓ N μ : ℝ) (hCfr : 1 ≤ Cfr) (hℓ : 0 < ℓ) (hℓN : ℓ < N)
include hD hq hM hCfr hℓ hℓN
theorem completeSourceRows_mass_positive (i ) :
    0 < (completeSourceRows C k D M q Cfr lam ℓ N μ).rowMass i := by
  obtain ⟨ha,hab⟩ := high_source_interval_numeric C M hM
  exact sourceRowMass_positive_actual d k D M q hD hq _ _ ha hab Cfr
    (by linarith) lam ℓ N μ hℓ hℓN i
theorem completeSourcePrior_probability (T ) (hT : 0 ≤ T)
    (hsmall : T * (highRowTotalMass (completeSourceRows C k D M q Cfr lam ℓ N μ).rowMass /
      highCenterMix C) / historyReferenceRho (3^d) ≤ 1 / (2+8*((3^d : ℕ):ℝ)^2))
    (t ) (ht : t ∈ Icc 0 T) :
    IsProbabilityMeasure (historyMarkedPrior (fun i j => j ∈ highNeighborLabels d k i) (3^d) t
      (highUnionLaw (completeSourceRows C k D M q Cfr lam ℓ N μ) (highCenterMix C))
      (highUnionActivation (completeSourceRows C k D M q Cfr lam ℓ N μ) (highCenterMix C))) :=
  highUnionSourcePrior_probability C _
    (completeSourceRows_guards C k D M q hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN)
    (completeSourceRows_mass_positive C hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN) T hT hsmall t ht
theorem completeSourceMass_prior_law (T ) (hT : 0 ≤ T)
    (hsmall : T * (highRowTotalMass (completeSourceRows C k D M q Cfr lam ℓ N μ).rowMass /
      highCenterMix C) / historyReferenceRho (3^d) ≤ 1 / (2+8*((3^d : ℕ):ℝ)^2))
    (t ) (ht : t ∈ Icc 0 T) :
    Measure.map (highUnionSourceMass C (completeSourceRows C k D M q Cfr lam ℓ N μ))
      (historyMarkedPrior (fun i j => j ∈ highNeighborLabels d k i) (3^d) t
        (highUnionLaw (completeSourceRows C k D M q Cfr lam ℓ N μ) (highCenterMix C))
        (highUnionActivation (completeSourceRows C k D M q Cfr lam ℓ N μ) (highCenterMix C))) =
    Measure.map (highUnionSourceMass C (completeSourceRows C k D M q Cfr lam ℓ N μ))
      (historyMarkedReference (fun i j => j ∈ highNeighborLabels d k i) (3^d)
        (highUnionLaw (completeSourceRows C k D M q Cfr lam ℓ N μ) (highCenterMix C))) :=
  have h_completeSourceMass_append_indicator_zero (j) (h) (S : Set ℝ) (hS : MeasurableSet S) : (∫ e, S.indicator (fun _ => 1)
      (highUnionSourceMass C (completeSourceRows C k D M q Cfr lam ℓ N μ)
        (historyMarkedAppend (fun i j => j ∈ highNeighborLabels d k i)
          (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j (h,e))) *
      highUnionActivation (completeSourceRows C k D M q Cfr lam ℓ N μ) (highCenterMix C) e
      ∂highUnionLaw (completeSourceRows C k D M q Cfr lam ℓ N μ) (highCenterMix C)) = 0 := by
    let a := C.densityLower+1/M
    let b := C.densityUpper-1/M
    obtain ⟨ha,hab⟩ := high_source_interval_numeric C M hM
    have hpos := sourceRowMass_positive_actual d k D M q hD hq a b ha hab Cfr (by linarith) lam ℓ N μ hℓ hℓN
    let β₀ : HighFrameIndex d D := ⟨fun _ => 0,by simp⟩
    let r₀ : HighResponseMarkIndex (HighFrameIndex d D) q := ((β₀,β₀),(false,false),0)
    exact highUnionSourceMass_append_indicator_zero_of_density_projection C (completeSourceRows C k D M q Cfr lam ℓ N μ)
      (completeSourceRows_guards C k D M q hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN) hpos
      (SourceRowDensityMark d D M q a b Cfr lam ℓ N μ)
      (sourceRowDensityProj d D M q a b Cfr lam ℓ N μ)
      (sourceRowDensityLift d D M q a b Cfr lam ℓ N μ r₀)
      (sourceRowDensityLift_measurable d D M q a b Cfr lam ℓ N μ r₀)
      (sourceRow_density_projection_slope d k D M q a b Cfr lam ℓ N μ r₀)
      (sourceRow_density_projection_intercept d k D M q a b Cfr lam ℓ N μ r₀)
      (sourceRow_density_observable_zero d k D M q a b Cfr lam ℓ N μ hpos) j h S hS
  highUnionSourceMass_prior_law_of_append_annihilation C _
    (completeSourceRows_guards C k D M q hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN)
    (completeSourceRows_mass_positive C hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN)
    T hT hsmall
    h_completeSourceMass_append_indicator_zero t ht
end
def highHistoryMassMomentConstant (d : ℕ) (a b : ℝ) : ℝ :=
  2^(2*d) * (b-a)^2 / 8
theorem highHistoryMassMomentConstant_pos (d a b) (hab : a < b) :
    0 < highHistoryMassMomentConstant d a b := by
  unfold highHistoryMassMomentConstant
  positivity
theorem highHistoryMassParameter_lowerSaddle (d m θ C a b x) :
    highHistoryMassParameter d (lowerSaddleGrid d m θ C x) a b =
      highHistoryMassMomentConstant d a b * (lowerSaddleH d m θ C x)^(d : ℝ) := by
  have h_highHistoryMassParameter_eq_hpower (k : ℕ) (hk : 0 < k) : highHistoryMassParameter d k a b = highHistoryMassMomentConstant d a b * ((k : ℝ)⁻¹)^d := by
    have h_highHistoryMassParameter_eq : highHistoryMassParameter d k a b = (2 : ℝ)^(2*d) * (b-a)^2 / (8 * (k : ℝ)^d) := by
      have hp : (k : ℝ)^d ≠ 0 := ne_of_gt (pow_pos (by exact_mod_cast hk) d)
      unfold highHistoryMassParameter
      rw [div_pow, mul_pow, Nat.mul_comm 2 d, pow_mul]
      field_simp
    rw [h_highHistoryMassParameter_eq]
    unfold highHistoryMassMomentConstant
    simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
    ring
  rw [h_highHistoryMassParameter_eq_hpower _ (by exact_mod_cast lowerSaddleGrid_positive (d : ℝ) m θ C x)]
  simp only [lowerSaddleH, Real.rpow_natCast]
theorem eventually_highHistoryMass_saddle_guard  (hd : 0 < d)
    {m θ cm : ℝ} (hm : 0 < m) (hθ : 0 < θ) (hcm : 0 < cm) (C a b : ℝ) (hab : a < b) :
    ∀ᶠ x : ℝ in atTop, 2 ≤ lowerSaddleGrid d m θ C x ∧
      8 * highHistoryMassParameter d (lowerSaddleGrid d m θ C x) a b * x ≤ cm / lowerSaddleM m x := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hCmgf := highHistoryMassMomentConstant_pos d a b hab
  have h_eventually_lowerSaddle_grid_and_mass {Cmgf : ℝ} (hCmgf : 0 < Cmgf) (gridThreshold) : ∀ᶠ x : ℝ in atTop, gridThreshold ≤ lowerSaddleGrid d m θ C x ∧
      8 * Cmgf * lowerSaddleMu d m θ C x ≤ cm / lowerSaddleM m x := by
    have hcap : 0 < cm / (8 * Cmgf) := by positivity
    have h_lowerSaddleM : Tendsto (fun x : ℝ => (lowerSaddleM m x ) * lowerSaddleMu d m θ C x) atTop (𝓝 0) := by
      have hh := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
        (lowerSaddleM_tendsto_atTop hm)).sub (lowerSaddleOmega_div_M_limit hdR hm hθ C)
      simp only [zero_sub] at hh
      have ht : Tendsto (fun x => Real.log (lowerSaddleM m x) - lowerSaddleOmega d m θ C x)
          atTop atBot := by
        apply tendsto_atBot_of_div_negative (lowerSaddleM_tendsto_atTop hm) _ (neg_neg_of_pos hθ)
        convert! hh using 1
        funext x
        change (Real.log (lowerSaddleM m x) - lowerSaddleOmega d m θ C x) / lowerSaddleM m x  =
          Real.log (lowerSaddleM m x) / lowerSaddleM m x  -
            lowerSaddleOmega d m θ C x / lowerSaddleM m x
        ring
      refine (Real.tendsto_exp_atBot.comp ht).congr' ?_
      filter_upwards [eventually_gt_atTop 0,
        (lowerSaddleM_tendsto_atTop hm).eventually (eventually_gt_atTop 0)] with x hx hM
      simp only [Function.comp_apply]
      rw [Real.exp_sub, Real.exp_log hM, lowerSaddleMu_eq_exp hx, Real.exp_neg]
      rfl
    filter_upwards [(tendsto_natCast_atTop_iff.1 (lowerSaddleGrid_tendsto_atTop hdR hm hθ C)).eventually (eventually_ge_atTop gridThreshold),
      (lowerSaddleM_tendsto_atTop hm).eventually (eventually_gt_atTop 0),
      h_lowerSaddleM.eventually (gt_mem_nhds hcap)] with x hx hM hmass
    refine ⟨hx, (le_div_iff₀ hM).2 ?_⟩
    have hh := (lt_div_iff₀ (by positivity : 0 < 8 * Cmgf)).1 hmass
    nlinarith only [hh]
  filter_upwards [(h_eventually_lowerSaddle_grid_and_mass hCmgf 2)] with x hx
  refine ⟨hx.1, ?_⟩
  rw [highHistoryMassParameter_lowerSaddle]
  unfold lowerSaddleMu at hx
  nlinarith only [hx.2]
section Pointwise
variable {d k D M q : ℕ} [NeZero d] [NeZero k] [LinearOrder (HighWindowLabels d k)]
    (C : ModelConstants d) (hD : 3 ≤ D) (hq : 1 ≤ q)
    (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
    (Cfr lam ell N mu : ℝ) (hCfr : 1 ≤ Cfr) (hell : 0 < ell) (hellN : ell < N)
include hD hq hM hCfr hell hellN
theorem completeSourceMass_prior_tilted_tail (hk : 2 ≤ k) (T ) (hT : 0 ≤ T)
    (hsmall : T*(highRowTotalMass (completeSourceRows C k D M q Cfr lam ell N mu).rowMass /
      highCenterMix C)/historyReferenceRho (3^d) ≤ 1/(2+8*((3^d:ℕ):ℝ)^2))
    (n : ℕ) (epsilon : ℝ)
    (hepsilon : 8*highHistoryMassParameter d k C.densityLower C.densityUpper*(n:ℝ) ≤ epsilon)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    (massPowerTilt
      (historyMarkedPrior (fun i j => j ∈ highNeighborLabels d k i) (3^d) t
        (highUnionLaw (completeSourceRows C k D M q Cfr lam ell N mu) (highCenterMix C))
        (highUnionActivation (completeSourceRows C k D M q Cfr lam ell N mu) (highCenterMix C)))
      (highUnionSourceMass C (completeSourceRows C k D M q Cfr lam ell N mu)) n).real
      {h | epsilon < |highUnionSourceMass C (completeSourceRows C k D M q Cfr lam ell N mu) h-1|} ≤
      2*Real.exp (-epsilon^2/(8*highHistoryMassParameter d k C.densityLower C.densityUpper)) := by
  have G := completeSourceRows_guards C k D M q hD hq hM Cfr lam ell N mu hCfr hell hellN
  rw [massPowerTilt_abs_event_eq_of_massLaw _ _ _ (highUnionSourceMass_measurable C _ G) n
    (completeSourceMass_prior_law C hD hq hM Cfr lam ell N mu hCfr hell hellN T hT hsmall t ht) epsilon]
  exact highUnionSourceMass_reference_tilted_tail C _ G hk n epsilon hepsilon
end Pointwise
def highCompleteSourceSaddleCoefficient  (C : ModelConstants d) : ℝ :=
  lowerSaddleCoefficient C.smoothness d (densityIntervalExponent C.densityLower C.densityUpper)
def highCompleteSourceSaddleTheta  (C : ModelConstants d) : ℝ :=
  lowerSaddleTheta C.smoothness d (densityIntervalExponent C.densityLower C.densityUpper)
def highCompleteSourceSaddleTail  (C : ModelConstants d) (Cω cm : ℝ) (n : ℕ) : ℝ :=
  lowerSaddleExceptionalTail d (highCompleteSourceSaddleCoefficient C) (highCompleteSourceSaddleTheta C) Cω
    (cm^2/(8*highHistoryMassMomentConstant d C.densityLower C.densityUpper)) n
section
set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] highUnionSourceDensity highUnionSourceState historyMarkedAppend
 theorem highUnionSourceResetDensity_product_zero_of_density_projection
     [NeZero k] [LinearOrder (HighWindowLabels d k)]
     [Fintype I]  [∀ i, MeasurableSpace (E i)]
    [∀ i, StandardBorelSpace (E i)] (C : ModelConstants d)
    (R : HighUnionRowData d k F I E) {M Cfr : ℝ} (G : HighUnionSourceGuards C M Cfr R)
    (hpos : ∀ i, 0 < R.rowMass i)
    (D : I → Type*) [∀ i, MeasurableSpace (D i)]
    (project : (i : I) → E i → D i) (lift : (i : I) → D i → E i)
    (hlift : ∀ i, Measurable (lift i))
    (hSlope : ∀ j i e x, R.rowSlope j i e x = R.rowSlope j i (lift i (project i e)) x)
    (hIntercept : ∀ i e, R.rowIntercept i e = R.rowIntercept i (lift i (project i e)))
    (hRowZero : ∀ i, ∀ H : D i → ℝ, Measurable H → ∀ L : ℝ,
      (∀ z, ‖H z‖ ≤ L) → (∫ e, R.rowActivation i e * H (project i e) ∂(R.rowLaw i)) = 0)
    (j : HighWindowLabels d k)
    (h n) (x : Fin n → Covariate d) :
    (∫ e, highUnionActivation R (highCenterMix C) e *
      ∏ i, highUnionSourceResetDensity C R j h e (x i) ∂highUnionLaw R (highCenterMix C)) = 0 := by
  let Fobs : HighUnionMark E → ℝ := fun e => ∏ i, highUnionSourceResetDensity C R j h e (x i)
  have hF : Measurable Fobs := Finset.measurable_fun_prod _ (fun i _ =>
    (highUnionSourceResetDensity_measurable C R G j h).comp (measurable_id.prodMk measurable_const))
  have hFb (e : HighUnionMark E) : ‖Fobs e‖ ≤ C.densityUpper^n := by
    simpa only [Real.norm_eq_abs,Fobs] using finite_density_product_abs_bound
      (fun i => highUnionSourceResetDensity C R j h e (x i)) C.densityUpper
      (by linarith [C.one_lt_densityUpper])
      (fun i => highUnionSourceResetDensity_abs_le C R G j h e (x i))
  have hp (i : I) (e : E i) (z : Covariate d) :
      highUnionSourceResetDensity C R j h (Sum.inl ⟨i,e⟩) z =
      highUnionSourceResetDensity C R j h (Sum.inl ⟨i,lift i (project i e)⟩) z := by
    unfold highUnionSourceResetDensity highUnionSourceDensity
    change (highUnionSourceState C R _).1 z = (highUnionSourceState C R _).1 z
    rw [highUnionSourceState_append,highUnionSourceState_append]
    change (if z ∈ highTorusPatch d k j then R.rowSlope j i e z * _ + R.rowIntercept i e else _) =
      (if z ∈ highTorusPatch d k j then R.rowSlope j i (lift i (project i e)) z * _ +
        R.rowIntercept i (lift i (project i e)) else _)
    rw [hSlope j i e z,hIntercept i e]
  have hrow (i : I) : (∫ e, R.rowActivation i e * Fobs (Sum.inl ⟨i,e⟩) ∂(R.rowLaw i)) = 0 := by
    let Hi : D i → ℝ := fun z => Fobs (Sum.inl ⟨i,lift i z⟩)
    have hHi : Measurable Hi := hF.comp
      (measurable_inl.comp ((rowSigmaMk_measurable i).comp (hlift i)))
    have he (e : E i) : Fobs (Sum.inl ⟨i,e⟩) = Hi (project i e) := by
      apply Finset.prod_congr rfl
      intro l _
      exact hp i e (x l)
    calc
      _ = ∫ e, R.rowActivation i e * Hi (project i e) ∂(R.rowLaw i) :=
        integral_congr_ae (Filter.Eventually.of_forall (fun e => congrArg _ (he e)))
      _ = 0 := hRowZero i Hi hHi (C.densityUpper^n) (fun z => hFb _)
  change (∫ e, highUnionActivation R (highCenterMix C) e * Fobs e ∂highUnionLaw R (highCenterMix C)) = 0
  rw [highUnionSource_bounded_action C R G hpos Fobs hF (C.densityUpper^n) hFb]
  simp only [hrow,Finset.sum_const_zero]
theorem completeSourceDensity_product_zero {d k D M q : ℕ}
    [NeZero d] [NeZero k] [LinearOrder (HighWindowLabels d k)]
    (C : ModelConstants d) (hD : 3 ≤ D) (hq : 1 ≤ q)
    (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
    (Cfr lam ℓ N μ ) (hCfr : 1 ≤ Cfr) (hℓ : 0 < ℓ) (hℓN : ℓ < N)
    (j h n) (x : Fin n → Covariate d) :
    (∫ e, highUnionActivation (completeSourceRows C k D M q Cfr lam ℓ N μ) (highCenterMix C) e *
      ∏ i, highUnionSourceResetDensity C (completeSourceRows C k D M q Cfr lam ℓ N μ)
        j h e (x i) ∂highUnionLaw (completeSourceRows C k D M q Cfr lam ℓ N μ) (highCenterMix C)) = 0 := by
  let a := C.densityLower+1/↑M
  let b := C.densityUpper-1/M
  obtain ⟨ha,hab⟩ := high_source_interval_numeric C ↑M hM
  have hpos := sourceRowMass_positive_actual d k D M q hD hq a b ha hab Cfr
    (by linarith) lam ℓ N μ hℓ hℓN
  let β₀ : HighFrameIndex d D := ⟨fun _ => 0,by simp⟩
  let r₀ : HighResponseMarkIndex (HighFrameIndex d D) q := ((β₀,β₀),(false,false),0)
  exact highUnionSourceResetDensity_product_zero_of_density_projection C (completeSourceRows C k D M q Cfr lam ℓ N μ)
    (completeSourceRows_guards C k D M q hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN) hpos
    (SourceRowDensityMark d D M q a b Cfr lam ℓ N μ)
    (sourceRowDensityProj d D M q a b Cfr lam ℓ N μ)
    (sourceRowDensityLift d D M q a b Cfr lam ℓ N μ r₀)
    (sourceRowDensityLift_measurable d D M q a b Cfr lam ℓ N μ r₀)
    (sourceRow_density_projection_slope d k D M q a b Cfr lam ℓ N μ r₀)
    (sourceRow_density_projection_intercept d k D M q a b Cfr lam ℓ N μ r₀)
    (sourceRow_density_observable_zero d k D M q a b Cfr lam ℓ N μ hpos) j h n x
set_option backward.isDefEq.respectTransparency false
end
section
open Set MeasureTheory
open scoped ENNReal ContDiff BigOperators
theorem highUnionSource_original_model_uniform  (C : ModelConstants d)
    (Q : LowSmoothnessTernaryConstants C) :
    ∃ Cfr η0 : ℝ, 1 ≤ Cfr ∧ 0 < η0 ∧
      ∀ U : ExtensionDomain d,
      ∀ k F : ℕ, ∀ (_ : NeZero k), ∀ (_ : LinearOrder (HighWindowLabels d k)), 4 ≤ k →
      ∀ (I : Type*) (_ : Fintype I) (E : I → Type*) (_ : (i : I) → MeasurableSpace (E i))
        (_ : (i : I) → StandardBorelSpace (E i))
        (R : HighUnionRowData d k F I E) (M : ℝ),
      HighUnionSourceGuards C M Cfr R →
      ∀ cf : ℝ, 0 ≤ cf → highWindowHolderConstant C * cf ≤ C.holderBound →
        cf * ↑k^(-C.smoothness) ≤ η0 →
      ∀ cm : ℝ, 0 ≤ cm → cm ≤ 1/C.densityUpper →
      ∀ h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E),
        |highUnionSourceMass C R h-1| ≤ cm/M →
      ∀ V : ℝ, |V-Q.v| ≤ Q.ρ →
      let p := highUnionSourceDensity C R h
      let f := highUnionSourceRegression C R (cf * ↑k^(-C.smoothness)) h
      ∃ hq : ∀ x y, 0 ≤ ternaryMass Q.a (f x) V y,
        Admissible (C.withDomain U) (normalizedDensityTernaryParameter p f Q.a V
          (highFrameField_contDiff d k _ _).continuous.measurable Q.a_pos.ne' hq) := by
  obtain ⟨Cfr, hCfr, hbound⟩ := highFrameField_original_model_bounds C
  obtain ⟨η0, hη0, hguard⟩ := highFrame_ternary_amplitude_guards Q
  refine ⟨Cfr, η0, hCfr, hη0, ?_⟩
  intro U k F hk0 horder hk I hI E hE hEB R M G cf hcf hcfH hη cm hcm hcmU h hmass V hV
  letI := hk0
  letI := horder
  letI := hI
  letI := hE
  letI := hEB
  let η := cf * ↑k^(-C.smoothness)
  let P := fun j => highFramePolynomial ((highUnionSourceState C R h).2 j)
  let f := highFrameField d k η P
  let p := highUnionSourceDensity C R h
  have hP (j) : frameCoefficientL1 (P j) ≤ Cfr⁻¹ :=
    (highFramePolynomial_coefficientL1_le _).trans (highUnionSourceState_coefficient_ball C R G h j)
  have hη0' : 0 ≤ η := by dsimp [η]; positivity
  obtain ⟨_, hsupη⟩ := hguard η hη0' hη
  obtain ⟨hvalue, _, _, hnorm⟩ := hbound k hk0 hk cf hcf P hP
  have hf (x : Covariate d) : |f x| ≤ Q.ρ :=
    (hvalue x).trans (hsupη.trans (by linarith [Q.ρ_pos]))
  have hlegal (x : Covariate d) := Q.legal (f x) V (hf x) hV
  have hq : ∀ x y, 0 ≤ ternaryMass Q.a (f x) V y :=
    fun x y => Q.c_pos.le.trans ((hlegal x).2.2.1 y)
  refine ⟨hq, ?_⟩
  have hF := highFrameField_contDiff d k η P
  have hp : Measurable p :=
    (highUnionSourceDensity_joint_measurable C R G).comp (measurable_const.prodMk measurable_id)
  have hraw : ∀ᵐ x ∂cubeVolume d,
      C.densityLower+1/M ≤ p x ∧ p x ≤ C.densityUpper-1/M :=
    Filter.Eventually.of_forall (fun x => highUnionSourceDensity_interval C R G h x)
  have hM := (highCenterResolution_guards C M G.resolution).1
  have hM0 : 0 < M := by linarith
  have hmass0 : 0 < highRawDensityMass p := lt_of_lt_of_le (by norm_num)
    (high_raw_mass_lower C M cm (highRawDensityMass p) hM hcm hcmU hmass)
  have : IsFiniteMeasure (cubeVolume d) := by
    constructor
    rw [cubeVolume_univ]
    exact ENNReal.one_lt_top
  have hbound : ∀ᵐ x ∂cubeVolume d, ‖p x‖ ≤ C.densityUpper := by
    filter_upwards [hraw] with x hx
    have hp0 : 0 ≤ p x := by linarith [C.densityLower_pos, one_div_pos.mpr hM0]
    rw [Real.norm_eq_abs, abs_of_nonneg hp0]
    linarith [one_div_pos.mpr hM0]
  have h_highRawDensity_integrable := (integrable_const C.densityUpper).mono' hp.aestronglyMeasurable hbound
  refine ⟨highNormalizedDensity_measurable p hp, hF.continuous.measurable,
    highNormalizedDensity_bounds C M cm hM hcm hcmU p hraw hmass,
    highNormalizedDensity_normalized p h_highRawDensity_integrable (by filter_upwards [hraw] with x hx; change 0 ≤ p x; linarith [C.densityLower_pos, one_div_pos.mpr hM0]) hmass0, ?_,
    (hlegal 0).1.le, (hlegal 0).2.1.le, ?_⟩
  · refine ⟨f, fun _ _ => rfl, (hF.of_le (by simp)).contDiffOn, ?_⟩
    exact (hnorm U.carrier).trans (ENNReal.ofReal_le_ofReal hcfH)
  · apply Filter.Eventually.of_forall
    intro x
    refine ⟨ternary_error_integrable Q.a V f hF.continuous.measurable x _,
      ternary_error_integrable Q.a V f hF.continuous.measurable x _,
      ternary_error_integrable Q.a V f hF.continuous.measurable x _,
      ternary_error_mean Q.a V f hF.continuous.measurable x Q.a_pos.ne' (hq x),
      ternary_error_variance Q.a V f hF.continuous.measurable x Q.a_pos.ne' (hq x), ?_⟩
    exact (ternary_error_fourth Q.a V f hF.continuous.measurable x Q.a_pos.ne' (hq x)).trans_le
      (by simpa only [ternary_fourth_central_moment _ _ _ Q.a_pos.ne', ModelConstants.withDomain] using (hlegal x).2.2.2)
end
theorem highUnionSource_ternary_floor_uniform  (C : ModelConstants d)
    (Q : LowSmoothnessTernaryConstants C) :
    ∃ Cfr η0, 1 ≤ Cfr ∧ 0 < η0 ∧
      ∀ k F : ℕ, ∀ (_ : NeZero k), ∀ (_ : LinearOrder (HighWindowLabels d k)), 4 ≤ k →
      ∀ (I : Type*) (_ : Fintype I) (E : I → Type*) (_ : (i : I) → MeasurableSpace (E i))
        (R : HighUnionRowData d k F I E) (M : ℝ),
      HighUnionSourceGuards C M Cfr R →
      ∀ cf : ℝ, 0 ≤ cf → cf * ↑k^(-C.smoothness) ≤ η0 →
      ∀ h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E),
      ∀ V : ℝ, |V-Q.v| ≤ Q.ρ →
      ∀ x y, Q.c ≤ ternaryMass Q.a
        (highUnionSourceRegression C R (cf * ↑k^(-C.smoothness)) h x) V y := by
  obtain ⟨Cfr,hCfr,hbound⟩ := highFrameField_original_model_bounds C
  obtain ⟨η0,hη0,hguard⟩ := highFrame_ternary_amplitude_guards Q
  refine ⟨Cfr,η0,hCfr,hη0,?_⟩
  intro k F hk0 horder hk I hI E hE R M G cf hcf hη h V hV x y
  letI := hk0
  letI := horder
  letI := hI
  letI := hE
  let η := cf * ↑k^(-C.smoothness)
  let P := fun j => highFramePolynomial ((highUnionSourceState C R h).2 j)
  have hP (j) : frameCoefficientL1 (P j) ≤ Cfr⁻¹ :=
    (highFramePolynomial_coefficientL1_le _).trans (highUnionSourceState_coefficient_ball C R G h j)
  obtain ⟨_, hηsup⟩ := hguard η (by dsimp [η]; positivity) hη
  have hv := (hbound k hk0 hk cf hcf P hP).1 x
  exact (Q.legal _ V (hv.trans (hηsup.trans (by linarith [Q.ρ_pos]))) hV).2.2.1 y
theorem HighUnionSourceGuards.mono_frame  {I : Type*} [Fintype I]
    {E : I → Type*} [∀ i, MeasurableSpace (E i)]
    {C : ModelConstants d} {M Cfr Cfr' : ℝ} {R : HighUnionRowData d k F I E}
    (G : HighUnionSourceGuards C M Cfr R) (hfr : 1 ≤ Cfr') (hle : Cfr' ≤ Cfr) :
    HighUnionSourceGuards C M Cfr' R := by
  refine { G with frame := hfr, vector_ball := ?_ }
  intro i e
  exact (G.vector_ball i e).trans ((inv_le_inv₀ (by linarith)
    (by linarith)).mpr hle)
section
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
def highNormalizedParameterPath (T ) (hT : 0 ≤ T) (a v η ) (ha : a ≠ 0)
    (p F : Ω → Covariate d → ℝ) (hF : Measurable (Function.uncurry F))
    (hq : ∀ t ∈ Icc 0 T, ∀ ω x y, 0 ≤ ternaryMass a (F ω x) (v-η^2*t) y)
    (t : ℝ) (ω : Ω) : RegressionParameter d :=
  if ht : t ∈ Icc 0 T then
    normalizedDensityTernaryParameter (p ω) (F ω) a (v-η^2*t) hF.of_uncurry_left ha (hq t ht ω)
  else
    normalizedDensityTernaryParameter (p ω) (F ω) a v hF.of_uncurry_left ha
      (fun x y => by simpa using hq 0 ⟨le_rfl,hT⟩ ω x y)
theorem highNormalizedParameterPath_apply (T : ℝ) (hT : 0 ≤ T) (a v η : ℝ) (ha : a ≠ 0)
    (p F : Ω → Covariate d → ℝ) (hF : Measurable (Function.uncurry F))
    (hq : ∀ t ∈ Icc 0 T, ∀ ω x y, 0 ≤ ternaryMass a (F ω x) (v-η^2*t) y)
    (t ht ω) :
    highNormalizedParameterPath T hT a v η ha p F hF hq t ω =
      normalizedDensityTernaryParameter (p ω) (F ω) a (v-η^2*t) hF.of_uncurry_left ha (hq t ht ω) := by
  unfold highNormalizedParameterPath
  rw [dif_pos ht]
end
theorem LowSmoothnessTernaryConstants.effective_interval 
    {C : ModelConstants d} (Q : LowSmoothnessTernaryConstants C)
     (hV : |V-Q.v| ≤ Q.ρ) : V ∈ Icc C.varianceLower (effectiveVarianceUpper C) := by
  have h := Q.legal 0 V (by simpa using Q.ρ_pos.le) hV
  have hp := Q.c_pos.trans_le (h.2.2.1 1)
  have : 0 < 1 - V / Q.a^2 := by simpa [ternaryMass] using hp
  have h_uniformZeroParameter_admissible : ∃ θ : RegressionParameter d, Admissible C θ ∧ θ.variance = V := by
    have hp : ∀ y, 0 ≤ ternaryMass Q.a 0 V y := by
      apply fun y => (ternary_mass_positive Q.a 0 V Q.a_pos (by simpa using ((div_lt_one (sq_pos_of_pos Q.a_pos)).mp (by linarith)))
        (by simpa using (C.varianceLower_pos.trans_le h.1.le)) y).le
    let θ := uniformZeroParameter d Q.a V Q.a_pos.ne' hp
    refine ⟨θ, ?_, rfl⟩
    refine ⟨measurable_const, measurable_const, ?_, ?_, ?_, h.1.le, h.2.1.le, ?_⟩
    · exact Filter.Eventually.of_forall (fun x =>
        ⟨C.densityLower_lt_one.le, C.one_lt_densityUpper.le⟩)
    · simp only [θ, uniformZeroParameter, ENNReal.ofReal_one, lintegral_const, one_mul]
      exact cubeVolume_univ d
    · refine ⟨fun _ => 0, fun _ _ => rfl, contDiffOn_const, ?_⟩
      rw [holderNorm_zero]
      exact zero_le
    · apply Filter.Eventually.of_forall
      intro x
      simp only [θ, uniformZeroParameter, Kernel.const_apply]
      refine ⟨ternaryMeasure_integrable Q.a 0 V _, ternaryMeasure_integrable Q.a 0 V _,
        ternaryMeasure_integrable Q.a 0 V _, ternaryMeasure_mean Q.a 0 V Q.a_pos.ne' hp, ?_, ?_⟩
      · simpa using ternaryMeasure_variance Q.a 0 V Q.a_pos.ne' hp
      · have he := ternaryMeasure_fourthMoment Q.a 0 V Q.a_pos.ne' hp
        simp only [sub_zero, zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 4 ≠ 0),
          mul_zero, add_zero] at he
        exact he.trans_le (by have hf := h.2.2.2; rw [ternary_fourth_central_moment Q.a 0 V Q.a_pos.ne'] at hf; simpa using hf)
  obtain ⟨θ,hθ,hθV⟩ := h_uniformZeroParameter_admissible
  simpa only [hθV,effectiveVarianceUpper] using admissible_variance_effective_interval C θ hθ
theorem intervalIntegral_sqrt_energy_le (f : ℝ → ℝ) (T M : ℝ) (hT : 0 ≤ T)
    (hi : IntervalIntegrable (fun t => Real.sqrt (f t)) volume 0 T)
    (hbound : ∀ t ∈ Icc 0 T, f t ≤ M) :
    (∫ t in ↑0..T, Real.sqrt (f t)) ≤ T * Real.sqrt M := by
  have h := intervalIntegral.integral_mono_on hT hi
    (intervalIntegrable_const (c := Real.sqrt M))
    (fun t ht => Real.sqrt_le_sqrt (hbound t ht))
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] using h
attribute [local irreducible] highUnionSourceDensity highUnionSourceRegression highUnionSourceState
  historyMarkedPrior massPowerNormalizer highRawDensityMass highMarginalRealScore highRealSampleKernel
abbrev HighCompleteSourceHistory {d : ℕ} (C : ModelConstants d) (k D M q : ℕ)
    [NeZero k] [LinearOrder (HighWindowLabels d k)] (Cfr lam ell N mu : ℝ) :=
  HistoryMarked (fun i j => j ∈ highNeighborLabels d k i)
    (HighUnionMark (SourceRowMark d D M q (C.densityLower+1/M)
      (C.densityUpper-1/M) Cfr lam ell N mu))
end
variable {rho eta0 B I eta N tau c0 cf : ℝ}
def highPathConstant (Δ : ℕ) (rho eta0 : ℝ) : ℝ :=
  min 1 (min (historyReferenceRho Δ / (2 + 8 * Δ ^ 2)) (rho / eta0 ^ 2))
theorem highPathConstant_pos (Δ )  (hrho : 0 < rho)
    (heta0 : 0 < eta0) : 0 < highPathConstant Δ rho eta0 := by
  exact lt_min (by norm_num) (lt_min
    (div_pos (historyReferenceRho_pos Δ) (by positivity)) (div_pos hrho (by positivity)))
theorem highPath_update_budget (Δ ) 
    (hrho : 0 < rho) (heta0 : 0 < eta0) (hB : 0 ≤ B) (hI : 0 ≤ I) :
    localScorePathLength (highPathConstant Δ rho eta0) B I * B / historyReferenceRho Δ ≤
      1 / (2 + 8 * Δ ^ 2) := by
  have hb : localScorePathLength (highPathConstant Δ rho eta0) B I * B ≤
      highPathConstant Δ rho eta0 := by
    have h := localScorePathLength_energy_le (highPathConstant_pos Δ hrho heta0).le hI hB
    simpa only [localScorePathLength, add_right_comm 1 I B] using h
  apply (div_le_iff₀ (historyReferenceRho_pos Δ)).mpr
  have h := hb.trans ((min_le_right _ _).trans (min_le_left _ _))
  simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using h
theorem highPath_variance_budget (Δ ) 
    (hrho : 0 < rho) (heta0 : 0 < eta0) (hB : 0 ≤ B) (hI : 0 ≤ I)
    (heta : 0 ≤ eta) (hetaU : eta ≤ eta0) :
    eta ^ 2 * localScorePathLength (highPathConstant Δ rho eta0) B I ≤ rho := by
  have hc := highPathConstant_pos Δ hrho heta0
  have h_localScorePathLength_le_constant {c} (hc : 0 ≤ c) : localScorePathLength c B I ≤ c := by
    apply (div_le_iff₀ (by linarith only [hB, hI] : 0 < 1 + B + I)).mpr
    simpa only [mul_one] using (mul_le_mul_of_nonneg_left (by linarith only [hB, hI] : 1 ≤ 1 + B + I) hc)
  have hlen := h_localScorePathLength_le_constant hc.le
  have hlen0 := (localScorePathLength_pos hc hB hI).le
  have he2  := (sq_le_sq₀ heta heta0.le).mpr hetaU
  have hcb : highPathConstant Δ rho eta0 ≤ rho / eta0 ^ 2 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hbudget := (le_div_iff₀ (by positivity)).mp hcb
  exact (mul_le_mul he2 hlen hlen0 (sq_nonneg _)).trans (by nlinarith only [hbudget])
theorem score_cost_scaled_numeric {c B I eta score K E : ℝ} (hc : 0 < c)
    (hB : 0 ≤ B) (hI : 0 ≤ I) (hscore0 : 0 ≤ score)
    (hscore : score ≤ localScorePathLength c B I * I)
    (hK : 1 ≤ K) (hE : 0 ≤ E) (hIE : I ^ 2 = K * E) :
    c ^ 2 / (3 * K * (2 + c) ^ 2) * eta ^ 4 / (1 + B ^ 2 + E) ≤
      eta ^ 4 * (localScorePathLength c B I) ^ 2 / (2 + score) ^ 2 := by
  have hden : 1 + B ^ 2 + I ^ 2 ≤ K * (1 + B ^ 2 + E) := by
    rw [hIE]
    have hm := mul_le_mul_of_nonneg_right hK (by positivity : 0 ≤ 1 + B ^ 2)
    nlinarith only [hm]
  have hh := div_le_div_of_nonneg_left
    (by positivity : 0 ≤ c ^ 2 / (3 * (2 + c) ^ 2) * eta ^ 4)
    (by positivity) hden
  have h_score_cost_numeric : c ^ 2 / (3 * (2 + c) ^ 2) * eta ^ 4 / (1 + B ^ 2 + I ^ 2) ≤
      eta ^ 4 * (localScorePathLength c B I) ^ 2 / (2 + score) ^ 2 := by
    have : 0 < 1 + B + I := by linarith only [hB, hI]
    have hsc  := hscore.trans (localScorePathLength_energy_le hc.le hB hI)
    have hscpos : 0 < 2 + score := by linarith only [hscore0]
    have hcpos : 0 < 2 + c := by linarith only [hc]
    have : 0 < 1 + B ^ 2 + I ^ 2 := by
      positivity
    have hsq : (2 + score) ^ 2 ≤ (2 + c) ^ 2 := by
      nlinarith only [hsc, hscpos, hcpos]
    have hprod : (2 + score) ^ 2 * (1 + B + I) ^ 2 ≤
        3 * (2 + c) ^ 2 * (1 + B ^ 2 + I ^ 2) := by
      have h_three_term_square_le : (1 + B + I) ^ 2 ≤ 3 * (1 + B ^ 2 + I ^ 2) := by
        nlinarith only [sq_nonneg (1 - B), sq_nonneg (1 - I), sq_nonneg (B - I)]
      calc
        _ ≤ (2 + c) ^ 2 * (1 + B + I) ^ 2 :=
          mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
        _ ≤ (2 + c) ^ 2 * (3 * (1 + B ^ 2 + I ^ 2)) :=
          mul_le_mul_of_nonneg_left h_three_term_square_le (sq_nonneg _)
        _ = _ := by ring
    calc
      _ = c ^ 2 * eta ^ 4 / (3 * (2 + c) ^ 2 * (1 + B ^ 2 + I ^ 2)) := by
        field_simp
      _ ≤ c ^ 2 * eta ^ 4 / ((2 + score) ^ 2 * (1 + B + I) ^ 2) := div_le_div_of_nonneg_left (by positivity) (by positivity) hprod
      _ = _ := by
        rw [localScorePathLength]
        field_simp
  apply le_trans _ (h_score_cost_numeric)
  convert hh using 1 <;> field_simp
def sourceResponseCost (q : ℕ) (C : ℝ) : ℝ :=
  (∑ h : Fin (2*q+2), |responseWeight q h|) * (2*C^2)
theorem sourceResponseCost_nonneg (q C) : 0 ≤ sourceResponseCost q C := by
  unfold sourceResponseCost
  positivity
theorem higherBandRowMass_le_activityCap_of_fine (d r m D q ) (hr : 2 ≤ r) (hD : 1 ≤ D)
    (a b ) (ha : 0 < a) (hab : a < b) (C lam L T )
    (hT : 1 ≤ T) (fine ) (hLT : fine = true → L ≤ T) :
    higherBandRowMass d r m D q a b C lam L T fine ≤ higherBandRowActivityCap d r m D q a b C lam T := by
  have h_higherBandRowMass_le_activityCap (L) (T) (hT : 1 ≤ T) (hLT : L ≤ T) (fine) : higherBandRowMass d r m D q a b C lam L T fine ≤ higherBandRowActivityCap d r m D q a b C lam T := by
    letI := higherBandCarrierMeasure_finite d r L T hT fine
    rw [higherBandRowMass_eq_variation d r m D q a b C lam L T hT fine]
    have h := highPacketSignedMeasure_exponential_cost (higherBandCarrierMeasure d r L T fine)
      a b ha hab m r D q (by omega) hD C (higherBandCarrierAmplitude d r D lam fine)
      (higherBandCarrierAmplitude_measurable d r D lam fine)
      (higherBandCarrierAmplitude_cost_integrable d r D lam L T hT fine)
    apply h.trans
    apply mul_le_mul_of_nonneg_left
    have h_higherBandCarrier_cost_integral_le : (∫ ζ, separatedMatrixCost (higherBandCarrierAmplitude d r D lam fine) ζ
        ∂higherBandCarrierMeasure d r L T fine) ≤ higherBandInterpolationCap d r lam T := by
      cases fine
      · have h := cardinal_separated_cost_integral_le (d := d) (D := D) hr lam hT
        have : 0 ≤ r * (1024 * |lam| * d^2)^(r-1) * T^2 * (1+Real.log T)^(r-2) := by
          have : 0 ≤ 1 + Real.log T := add_nonneg (by norm_num) (Real.log_nonneg hT)
          positivity
        exact h.trans (by dsimp [higherBandInterpolationCap]; nlinarith)
      · exact cardinal_band_cost_integral_le hr lam L hT hLT
    · exact h_higherBandCarrier_cost_integral_le
    · positivity
  cases fine
  · exact h_higherBandRowMass_le_activityCap 1 T hT hT false
  · exact h_higherBandRowMass_le_activityCap L T hT (hLT rfl) true
def higherBandFilteredMass (d D M q : ℕ) (a b C lam ℓ N μ : ℝ) (i : Fin (D-2) × Bool) : ℝ :=
  if HigherBandFamilySelected d D M q a b C lam ℓ N μ i then
    higherBandRowMass d (higherBandFamilyTarget i) (higherBandFamilyGuardDegree M i) D q
      a b C lam ℓ (higherBandFamilyUpper d ℓ N μ i) i.2 else 0
def higherBandCoarseActivity (d D M q : ℕ) (a b C lam ℓ N μ : ℝ) (j : Fin (D-2)) : ℝ :=
  higherBandFilteredMass d D M q a b C lam ℓ N μ (j,false)
def higherBandFineActivity (d D M q : ℕ) (a b C lam ℓ N μ : ℝ) (j : Fin (D-2)) : ℝ :=
  higherBandFilteredMass d D M q a b C lam ℓ N μ (j,true)
theorem finite_geometric_tail_le_two_mul {q : ℝ} (hq : 0 ≤ q) (hqh : q ≤ 1 / 2)
    (m : ℕ) : (∑ j ∈ Finset.range m, q ^ (j + 1)) ≤ 2 * q := by
  calc
    _ = q * ∑ j ∈ Finset.range m, q ^ j := by simp_rw [pow_succ]; rw [Finset.mul_sum]; ring
    _ ≤ q * ∑ j ∈ Finset.range m, (1 / ↑2) ^ j :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => pow_le_pow_left₀ hq hqh j) hq
    _ ≤ q * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le m) hq
    _ = _ := mul_comm _ _
theorem finite_activity_fin_tail_le  (hK : 0 ≤ K) (hq : 0 ≤ q)
    (hqh : q ≤ 1/2) (m : ℕ) (B : Fin m → ℝ)
    (hB : ∀ j, B j ≤ K*q^(j.val+1)) :
    (∑ j, B j) ≤ 2*K*q := by
  calc
    _ ≤ ∑ j : Fin m, K*q^(j.val+1) := Finset.sum_le_sum fun j _ => hB j
    _ = K * ∑ j : Fin m, q^(j.val+1) := (Finset.mul_sum _ _ _).symm
    _ = K * ∑ j ∈ Finset.range m, q^(j+1) := by
      exact congrArg (fun t : ℝ => K*t) (Fin.sum_univ_eq_sum_range (fun j => q^(j+1)) m)
    _ ≤ K*(2*q) := mul_le_mul_of_nonneg_left (finite_geometric_tail_le_two_mul hq hqh m) hK
    _ = _ := by ring
theorem source_exteriorTau_nonneg  (ha : 0 < a) (hab : a < b) :
    0 ≤ exteriorTau ((a+b)/(b-a)) := by
  apply exteriorTau_nonneg
  apply (le_div_iff₀ (sub_pos.mpr hab)).mpr
  linarith
def sourceActivityConstant (d q : ℕ) (C B lam : ℝ) : ℝ :=
  B^2 * sourceResponseCost q C * (1+512*d) + B * sourceResponseCost q C +
    4 * higherBandGeometricPrefactor B (higherBandInterpolationBase d lam) (sourceResponseCost q C)
theorem sourceRows_activity_bound {d k D M q : ℕ} [NeZero d] (hd : 0 < d) (hD : 1 ≤ D)
    (a b C lam ℓ N μ B q1 q2 ) (ha : 0 < a) (hab : a < b)
    (hℓ : 0 ≤ ℓ) (hℓN : ℓ ≤ N) (hN : 1 ≤ N) (hμ : 0 ≤ μ) (hbase1 : μ*(1+Real.log N) ≤ 1)
    (hB : 0 ≤ B) (hbB : ordinaryDensityActivityBase a b ≤ B)
    (hq1 : q1 = higherBandGeometricRatio d D
      (higherBandGeometricConstant B (higherBandInterpolationBase d lam)) (1+Real.log N) (μ*(1+Real.log N)) 1)
    (hq2 : q2 = higherBandGeometricRatio d D
      (higherBandGeometricConstant B (higherBandInterpolationBase d lam)) (1+Real.log N) (μ*(1+Real.log N)) 2)
    (hq1h : q1 ≤ 1/2) (hq21 : q2 ≤ q1) (hsmall : (D : ℝ)^2*q1 ≤ 1)
    (hcoarse : Real.exp ((D : ℝ)*exteriorTau ((a+b)/(b-a)))*ℓ ≤ N)
    (hsingle : (D : ℝ)*Real.exp ((D : ℝ)*exteriorTau ((a+b)/(b-a))) ≤ N)
    (hpair : (D : ℝ)^2*Real.exp ((D : ℝ)*exteriorTau ((a+b)/(b-a)))*ℓ^2 ≤ 2*N^2) :
    highRowTotalMass (sourceRowData d k D M q a b C lam ℓ N μ).rowMass ≤
      sourceActivityConstant d q C B lam * N^2 * Real.exp (M*exteriorTau ((a+b)/(b-a))) := by
  let A := ordinaryDensityActivityBase a b
  let EM := Real.exp (M*exteriorTau ((a+b)/(b-a)))
  let ED := Real.exp (D*exteriorTau ((a+b)/(b-a)))
  have hED : 1 ≤ ED := Real.one_le_exp (mul_nonneg (Nat.cast_nonneg _) (source_exteriorTau_nonneg ha hab))
  have hEM : 1 ≤ EM := Real.one_le_exp (mul_nonneg (Nat.cast_nonneg _) (source_exteriorTau_nonneg ha hab))
  have hunit : D^2*ED ≤ N^2 := by
    have h1 := mul_le_mul_of_nonneg_left hED (by positivity : 0 ≤ D^2*ED)
    have h2 := pow_le_pow_left₀ (by positivity : 0 ≤ D*ED) hsingle 2
    nlinarith only [h1, h2]
  have h_finePairTotalMass_activity_bound : highRowTotalMass (finePairRowData d k D M q a b C ℓ N).rowMass ≤
      (ordinaryDensityActivityBase a b)^2 * sourceResponseCost q C * (1+512*d) *
        N^2 * Real.exp (M*exteriorTau ((a+b)/(b-a))) := by
    let K := (ordinaryDensityActivityBase a b)^2 * sourceResponseCost q C
    let EM := Real.exp (M*exteriorTau ((a+b)/(b-a)))
    have hK : 0 ≤ K := mul_nonneg (sq_nonneg _) (sourceResponseCost_nonneg q C)
    have hEM : 1 ≤ EM := Real.one_le_exp (mul_nonneg (Nat.cast_nonneg _) (source_exteriorTau_nonneg ha hab))
    have hu : finePairRowMass d D M q a b C ℓ N .unit ≤ K*N^2 := by
      have h_finePairRowMass_unit_le : finePairRowMass d D M q a b C ℓ N .unit ≤
      (ordinaryDensityActivityBase a b)^2 * D^2 *
        Real.exp (D * exteriorTau ((a+b)/(b-a))) * sourceResponseCost q C := by
        rw [finePairRowMass_unit]
        have hc : 0 ≤ (∑ h : Fin (2*q+2), |responseWeight q h|) * (2*C^2) := by positivity
        have hm := mul_le_mul (densityPacketWeight_exponential_cost a b ha hab D 2 D (by norm_num) hD) (finePairUnitMatrix_l1_le d D) (Finset.sum_nonneg fun _ _ =>
          Finset.sum_nonneg fun _ _ => abs_nonneg _) (by positivity)
        have hh := mul_le_mul_of_nonneg_left hm hc
        dsimp [ordinaryDensityActivityBase, sourceResponseCost, spatialMatrixL1] at *
        nlinarith only [hh]
      apply h_finePairRowMass_unit_le.trans
      calc
        _ = K*(D^2*Real.exp (D*exteriorTau ((a+b)/(b-a)))) := by dsimp [K]; ring
        _ ≤ K*N^2 := mul_le_mul_of_nonneg_left hunit hK
    have hc : finePairRowMass d D M q a b C ℓ N .coarse ≤ 256*d*K*N^2 := by
      have h_finePairRowMass_coarse_le : finePairRowMass d D M q a b C ℓ N .coarse ≤
      (ordinaryDensityActivityBase a b)^2 * D^2 *
        Real.exp (D * exteriorTau ((a+b)/(b-a))) * sourceResponseCost q C *
          ((128 * d) * ℓ^2) := by
        rw [finePairRowMass_coarse d D M q a b C ℓ N hℓ]
        have hmat := mul_le_mul_of_nonneg_right (finePairDistanceMatrix_l1_le d D)
          (by positivity : 0 ≤ ℓ^2/2)
        have hm := mul_le_mul (densityPacketWeight_exponential_cost a b ha hab D 2 D (by norm_num) hD) hmat (by positivity : 0 ≤
          (∑ i, ∑ j, |finePairDistanceMatrix d D i j|) * (ℓ^2/2)) (by positivity)
        have hh := mul_le_mul_of_nonneg_left hm (sourceResponseCost_nonneg q C)
        dsimp [ordinaryDensityActivityBase, sourceResponseCost, spatialMatrixL1] at *
        nlinarith only [hh]
      apply h_finePairRowMass_coarse_le.trans
      calc
        _ = (128*d*K)*(D^2*Real.exp (D*exteriorTau ((a+b)/(b-a)))*ℓ^2) := by dsimp [K]; ring
        _ ≤ (128*d*K)*(2*N^2) := mul_le_mul_of_nonneg_left hpair (by positivity)
        _ = _ := by ring
    have h_finePairRowMass_fine_le : finePairRowMass d D M q a b C ℓ N .fine ≤
      (ordinaryDensityActivityBase a b)^2 *
        Real.exp (M * exteriorTau ((a+b)/(b-a))) * sourceResponseCost q C *
          ((256 * d) * N^2) := by
      rw [finePairRowMass_fine d D M q a b C ℓ N hℓ hℓN]
      have h_finePairDensityWeight_le_base : (∑ h : FinePairDensityIndex M, |finePairDensityWeight a b M h|) ≤
          2 * (ordinaryDensityActivityBase a b)^2 * Real.exp (M * exteriorTau ((a+b)/(b-a))) := by
        have hp : |finePairDensityPrefactor a b| = |b / densityMargin a b 0|^2 := by
          simp only [finePairDensityPrefactor, abs_div, abs_pow, div_pow]
        have he : Real.exp (2 * exteriorTau ((a+b)/(b-a))) ≤
            Real.exp (1 + exteriorTau ((a+b)/(b-a)))^2 := by
          rw [← Real.exp_nat_mul]
          apply Real.exp_le_exp.mpr
          norm_num
        have h_finePairDensityWeight_exponential_cost : (∑ h : FinePairDensityIndex M, |finePairDensityWeight a b M h|) ≤
          (2 * |finePairDensityPrefactor a b| * Real.exp (2 * exteriorTau ((a + b) / (b - a)))) *
            Real.exp (M * exteriorTau ((a + b) / (b - a))) := by
          rw [finePairDensityWeight_variation a b ha hab M]
          have he : Real.cosh ((M + 2 : ℕ) * exteriorTau ((a + b) / (b - a))) ≤
              Real.exp ((M + 2 : ℕ) * exteriorTau ((a + b) / (b - a))) := by
            rw [← exterior_rule_variation a b ha hab (M + 2) (by omega)]
            exact exterior_rule_variation_le_exp a b ha hab (M + 2) (by omega)
          apply (mul_le_mul_of_nonneg_left he (by positivity)).trans_eq
          rw [Nat.cast_add, Nat.cast_ofNat, add_mul, Real.exp_add]
          ring
        apply h_finePairDensityWeight_exponential_cost.trans
        rw [hp, ordinaryDensityActivityBase, mul_pow]
        have h0 := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 2 * |b / densityMargin a b 0|^2)
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        nlinarith only [h0]
      have hden := h_finePairDensityWeight_le_base
      have hdiff : 0 ≤ (N^2-ℓ^2)/2 := by nlinarith
      have hmat := mul_le_mul_of_nonneg_right (finePairDistanceMatrix_l1_le d D) hdiff
      have hmat' : (∑ i, ∑ j, |finePairDistanceMatrix d D i j|) * ((N^2-ℓ^2)/2) ≤
          (128 * d) * N^2 := by
        apply hmat.trans
        have hd0 : 0 ≤ d := Nat.cast_nonneg d
        nlinarith [hd0, sq_nonneg ℓ]
      have hm := mul_le_mul hden hmat' (by positivity : 0 ≤
        (∑ i, ∑ j, |finePairDistanceMatrix d D i j|) * ((N^2-ℓ^2)/2)) (by positivity)
      have hh := mul_le_mul_of_nonneg_left hm (sourceResponseCost_nonneg q C)
      dsimp [ordinaryDensityActivityBase, sourceResponseCost, spatialMatrixL1] at *
      nlinarith only [hh]
    have hf := h_finePairRowMass_fine_le
    have hu' : finePairRowMass d D M q a b C ℓ N .unit ≤ K*N^2*EM := by
      apply hu.trans
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hEM (by positivity)
    have hc' : finePairRowMass d D M q a b C ℓ N .coarse ≤ 256*d*K*N^2*EM := by
      apply hc.trans
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hEM (by positivity : 0 ≤ 256*d*K*N^2)
    have he : (Finset.univ : Finset FinePairRowTag) = {.unit, .coarse, .fine} := by
      ext i; cases i <;> simp
    change (∑ i, finePairRowMass d D M q a b C ℓ N i) ≤ _
    rw [he, Finset.sum_insert (show FinePairRowTag.unit ∉ ({.coarse, .fine} : Finset FinePairRowTag) by decide),
      Finset.sum_insert (show FinePairRowTag.coarse ∉ ({.fine} : Finset FinePairRowTag) by decide), Finset.sum_singleton]
    change _ ≤ K*(1+512*d)*N^2*EM
    dsimp [K, EM] at hu' hc'
    nlinarith only [hu', hc', hf]
  have hp' : highRowTotalMass (finePairRowData d k D M q a b C ℓ N).rowMass ≤
      B^2*sourceResponseCost q C*(1+512*d)*N^2*EM := by
    apply (h_finePairTotalMass_activity_bound).trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by dsimp [A, ordinaryDensityActivityBase]; positivity) hbB 2) (sourceResponseCost_nonneg q C))
        (by positivity)) (sq_nonneg N)) (Real.exp_pos _).le
  have h_singletonRowMass_exponential_bound : singletonRowMass d D q a b C ≤
      (Real.exp (1+exteriorTau ((a+b)/(b-a))) * |b/densityMargin a b 0|) * D *
      Real.exp (D*exteriorTau ((a+b)/(b-a))) *
      (∑ h : Fin (2*q+2), |responseWeight q h|) * (2*C^2) := by
    rw [singletonRowMass, highPacketMarkMass_eq_variation (Measure.dirac ()) a b D 1 D q C
      (fun _ => finePairUnitMatrix d D) (fun _ _ => measurable_const) (integrable_const _)]
    have h := highPacketSignedMeasure_exponential_cost (Measure.dirac ()) a b ha hab D 1 D q
      (by norm_num) hD C (fun _ => finePairUnitMatrix d D) (fun _ _ => measurable_const) (integrable_const _)
    simp only [pow_one, separatedMatrixCost, integral_dirac] at h
    apply h.trans
    exact (mul_le_mul_of_nonneg_left (finePairUnitMatrix_l1_le d D) (by positivity)).trans_eq (mul_one _)
  have hs := h_singletonRowMass_exponential_bound
  have hs' : singletonRowMass d D q a b C ≤ B*sourceResponseCost q C*N^2*EM := by
    apply hs.trans
    have h1 := mul_le_mul hbB hsingle (by positivity : 0 ≤ D*ED) hB
    have h2 := mul_le_mul_of_nonneg_right h1 (sourceResponseCost_nonneg q C)
    have hN2 : N ≤ N^2*EM := by
      have hsq : N ≤ N^2 := by nlinarith
      apply hsq.trans
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hEM (sq_nonneg N)
    have h3 := mul_le_mul_of_nonneg_left hN2 (mul_nonneg hB (sourceResponseCost_nonneg q C))
    dsimp [A, ED, ordinaryDensityActivityBase, sourceResponseCost] at h2
    dsimp [sourceResponseCost] at h3
    dsimp [ordinaryDensityActivityBase, sourceResponseCost] at hs ⊢
    nlinarith only [h2, h3]
  have h_higherBandFamily_activity_bound : highRowTotalMass (higherBandFamilyData d k D M q a b C lam ℓ N μ).rowMass ≤
      4 * higherBandGeometricPrefactor B (higherBandInterpolationBase d lam) (sourceResponseCost q C) *
        N^2 * Real.exp (M*exteriorTau ((a+b)/(b-a))) := by
    let K := higherBandGeometricPrefactor B (higherBandInterpolationBase d lam) (sourceResponseCost q C)
    let ED := Real.exp (D*exteriorTau ((a+b)/(b-a)))
    let EM := Real.exp (M*exteriorTau ((a+b)/(b-a)))
    have : 0 ≤ K := by
      dsimp [K, higherBandGeometricPrefactor, higherBandInterpolationBase, sourceResponseCost]
      positivity
    have hH : 0 ≤ 1+Real.log N := by linarith [Real.log_nonneg hN]
    have hq10 : 0 ≤ q1 := by rw [hq1]; unfold higherBandGeometricRatio higherBandGeometricConstant higherBandInterpolationBase; positivity
    have hq20 : 0 ≤ q2 := by rw [hq2]; unfold higherBandGeometricRatio higherBandGeometricConstant higherBandInterpolationBase; positivity
    have hτ : 0 ≤ exteriorTau ((a+b)/(b-a)) := by
      apply exteriorTau_nonneg
      apply (le_div_iff₀ (sub_pos.mpr hab)).mpr
      linarith
    have hEM : 1 ≤ EM := Real.one_le_exp (mul_nonneg (Nat.cast_nonneg M) hτ)
    have hc := finite_activity_fin_tail_le (K := K*D^2*ED*N*ℓ) (by positivity)
      hq10 hq1h (D-2) (higherBandCoarseActivity d D M q a b C lam ℓ N μ) (fun j => by
        have h_higherBandCoarseActivity_geometric_le : higherBandCoarseActivity d D M q a b C lam ℓ N μ j ≤
        higherBandGeometricPrefactor B (higherBandInterpolationBase d lam) (sourceResponseCost q C) *
        D^2 * Real.exp (D*exteriorTau ((a+b)/(b-a))) * (N*ℓ) *
        (higherBandGeometricRatio d D (higherBandGeometricConstant B (higherBandInterpolationBase d lam))
          (1+Real.log N) (μ*(1+Real.log N)) 1)^(j.val+1) := by
          unfold higherBandCoarseActivity higherBandFilteredMass
          split_ifs with hi
          · have hmass := higherBandRowMass_le_activityCap_of_fine d (j.val+3) D D q (by omega) hD
              a b ha hab C lam ℓ (min ℓ (higherBandTargetScale d (j.val+3) N μ)) hi.1 false (by intro h; cases h)
            have hcap := higherBandRowActivityCap_coarse_geometric_le (r := j.val+3) (D := D) (q := q)
              hd (by omega) a b C lam N μ ℓ B hN hμ hbase1 hi.1 hB hbB
            simpa [higherBandFamilyTarget, higherBandFamilyGuardDegree, higherBandFamilyUpper,
              sourceResponseCost, mul_assoc] using hmass.trans hcap
          · have : 0 ≤ 1+Real.log N := by linarith [Real.log_nonneg hN]
            unfold higherBandGeometricPrefactor higherBandInterpolationBase higherBandGeometricRatio
              higherBandGeometricConstant sourceResponseCost
            positivity
        have hh := h_higherBandCoarseActivity_geometric_le
        simpa only [← hq1, K, ED, mul_assoc] using hh)
    have hf := finite_activity_fin_tail_le (K := K*D^2*EM*N^2) (by positivity)
      hq20 (hq21.trans hq1h) (D-2) (higherBandFineActivity d D M q a b C lam ℓ N μ) (fun j => by
        have h_higherBandFineActivity_geometric_le : higherBandFineActivity d D M q a b C lam ℓ N μ j ≤
        higherBandGeometricPrefactor B (higherBandInterpolationBase d lam) (sourceResponseCost q C) *
        D^2 * Real.exp (M*exteriorTau ((a+b)/(b-a))) * N^2 *
        (higherBandGeometricRatio d D (higherBandGeometricConstant B (higherBandInterpolationBase d lam))
          (1+Real.log N) (μ*(1+Real.log N)) 2)^(j.val+1) := by
          unfold higherBandFineActivity higherBandFilteredMass
          split_ifs with hi
          · have hLT : ℓ ≤ higherBandTargetScale d (j.val+3) N μ := by
              simpa [higherBandFamilyTarget] using (hi.2.1 rfl).le
            have hmass := higherBandRowMass_le_activityCap_of_fine d (j.val+3) M D q (by omega) hD
              a b ha hab C lam ℓ (higherBandTargetScale d (j.val+3) N μ) hi.1 true (by intro _; exact hLT)
            have hcap := higherBandRowActivityCap_fine_geometric_le (r := j.val+3) (M := M) (D := D) (q := q)
              hd (by omega) a b C lam N μ B hN hμ hbase1 hi.1 hB hbB
            simpa [higherBandFamilyTarget, higherBandFamilyGuardDegree, higherBandFamilyUpper,
              sourceResponseCost, mul_assoc] using hmass.trans hcap
          · have : 0 ≤ 1+Real.log N := by linarith [Real.log_nonneg hN]
            unfold higherBandGeometricPrefactor higherBandInterpolationBase higherBandGeometricRatio
              higherBandGeometricConstant sourceResponseCost
            positivity
        have hh := h_higherBandFineActivity_geometric_le
        simpa only [← hq2, K, EM] using hh)
    have hsmall2 : D^2*q2 ≤ 1 :=
      (mul_le_mul_of_nonneg_left hq21 (sq_nonneg _)).trans hsmall
    have hc' : (∑ j, higherBandCoarseActivity d D M q a b C lam ℓ N μ j) ≤ 2*K*N^2 := by
      apply hc.trans
      calc
        _ = (2*K*N)*(ED*ℓ)*(D^2*q1) := by ring
        _ ≤ (2*K*N)*N*1 := mul_le_mul (mul_le_mul_of_nonneg_left hcoarse (by positivity))
          hsmall (by positivity) (by positivity)
        _ = _ := by ring
    have hf' : (∑ j, higherBandFineActivity d D M q a b C lam ℓ N μ j) ≤ 2*K*N^2*EM := by
      apply hf.trans
      calc
        _ = (2*K*N^2*EM)*(D^2*q2) := by ring
        _ ≤ (2*K*N^2*EM)*1 := mul_le_mul_of_nonneg_left hsmall2 (by positivity)
        _ = _ := mul_one _
    have h_higherBandFamily_totalMass_eq : highRowTotalMass (higherBandFamilyData d k D M q a b C lam ℓ N μ).rowMass =
        (∑ j : Fin (D-2), higherBandCoarseActivity d D M q a b C lam ℓ N μ j) +
        (∑ j : Fin (D-2), higherBandFineActivity d D M q a b C lam ℓ N μ j) := by
      change (∑ i : HigherBandFamilyIndex d D M q a b C lam ℓ N μ,
        higherBandRowMass d (higherBandFamilyTarget i.val) (higherBandFamilyGuardDegree M i.val) D q
          a b C lam ℓ (higherBandFamilyUpper d ℓ N μ i.val) i.val.2) = _
      rw [← Finset.sum_subtype (Finset.univ.filter (HigherBandFamilySelected d D M q a b C lam ℓ N μ))
        (by intro i; simp) (fun i => higherBandRowMass d (higherBandFamilyTarget i)
          (higherBandFamilyGuardDegree M i) D q a b C lam ℓ (higherBandFamilyUpper d ℓ N μ i) i.2), Finset.sum_filter, Fintype.sum_prod_type]
      simp only [Fintype.sum_bool, higherBandCoarseActivity, higherBandFineActivity,
        higherBandFilteredMass, Finset.sum_add_distrib]
      exact add_comm _ _
    rw [h_higherBandFamily_totalMass_eq]
    have hm := mul_le_mul_of_nonneg_left hEM (by positivity : 0 ≤ 2*K*N^2)
    change _ ≤ 4*K*N^2*EM
    nlinarith only [hc', hf', hm]
  have hh := h_higherBandFamily_activity_bound
  have h_sourceRowTotalMass_eq : highRowTotalMass (sourceRowData d k D M q a b C lam ℓ N μ).rowMass =
      highRowTotalMass (finePairRowData d k D M q a b C ℓ N).rowMass + singletonRowMass d D q a b C +
      highRowTotalMass (higherBandFamilyData d k D M q a b C lam ℓ N μ).rowMass := by
    simp only [highRowTotalMass, Fintype.sum_sum_type, sourceRowData, sourceRowComponent,
      highUnionRowRestrict, Fintype.sum_unique, singletonRowData, higherBandFamilyData, add_assoc]
  rw [h_sourceRowTotalMass_eq]
  dsimp [sourceActivityConstant]
  change _ ≤ _*N^2*EM
  nlinarith only [hp', hs', hh]
section
theorem source_pair_coarse_scale_le {D N tau c0 : ℝ} (hD : 0 ≤ D)
    (hc0 : 1 ≤ c0) (htau : tau ≤ c0) :
    D^2*Real.exp (tau*D)*(N*Real.exp (-c0*D))^2 ≤ 2*N^2 := by
  have he : Real.exp ((tau-2*c0)*D) ≤ Real.exp (-D) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have h_source_pair_polynomial_exponential_le : D^2*Real.exp (-D) ≤ 2 := by
    have hp := Real.pow_div_factorial_le_exp D hD 2
    norm_num only [Nat.factorial, Nat.cast_ofNat, Nat.cast_one] at hp
    have hs : D^2 ≤ 2*Real.exp D := by linarith
    have h := mul_le_mul_of_nonneg_right hs (Real.exp_pos (-D)).le
    have he : Real.exp D * Real.exp (-D) = 1 := by rw [← Real.exp_add]; simp
    calc _ ≤ 2*Real.exp D*Real.exp (-D) := h
         _ = 2 := by rw [mul_assoc,he,mul_one]
  have hid : D^2*Real.exp (tau*D)*(N*Real.exp (-c0*D))^2 =
      N^2*(D^2*Real.exp ((tau-2*c0)*D)) := by
    rw [mul_pow, ← Real.exp_nat_mul, show (tau-2*c0)*D = tau*D+↑2*(-c0*D) by norm_num; ring, Real.exp_add]
    ring
  rw [hid]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left he (sq_nonneg D)).trans (h_source_pair_polynomial_exponential_le)) (sq_nonneg N)
def sourceSaddleActivityConstant (d q : ℕ) (a b C lam : ℝ) : ℝ :=
  1 + sourceActivityConstant d q C
    (uniformOrdinaryDensityActivityBase a b (densityIntervalExponent a b+1)) lam
theorem sourceSaddleActivityConstant_positive (d q a b C lam)
    (ha : 0 < a) (hab : a < b) : 0 < sourceSaddleActivityConstant d q a b C lam := by
  have hB : 0 ≤ uniformOrdinaryDensityActivityBase a b (densityIntervalExponent a b+1) := by
    exact mul_nonneg (Real.exp_pos _).le (div_nonneg (sub_pos.mpr hab).le ha.le)
  have h_sourceActivityConstant_nonneg (B) (hB : 0 ≤ B) : 0 ≤ sourceActivityConstant d q C B lam := by
    unfold sourceActivityConstant higherBandGeometricPrefactor higherBandInterpolationBase sourceResponseCost
    positivity
  have := (h_sourceActivityConstant_nonneg _ hB)
  unfold sourceSaddleActivityConstant
  linarith
def sourceSaddleTotalMass (d k q : ℕ) (s a b C lam shift x : ℝ) : ℝ :=
  let tau := densityIntervalExponent a b
  let m := lowerSaddleCoefficient s d tau
  let theta := lowerSaddleTheta s d tau
  let M := lowerSaddleM m x
  highRowTotalMass (sourceRowData d k (lowerSaddleD (d : ℝ) m x) M q (a+(M : ℝ)⁻¹) (b-(M : ℝ)⁻¹) C lam (lowerAliasCutoff s (d : ℝ) m theta shift (tau+1) (shrunkDensityExponent a b) x) (lowerSaddleN s (d : ℝ) m theta shift (shrunkDensityExponent a b) x) (lowerSaddleMu (d : ℝ) m theta shift x)).rowMass
attribute [local irreducible] sourceRowData highRowTotalMass
def completeSourceSaddleRows {d : ℕ} (C : ModelConstants d)
    (q : ℕ) (Cfr lam Cω x : ℝ) :=
  let m := highCompleteSourceSaddleCoefficient C
  let theta := highCompleteSourceSaddleTheta C
  completeSourceRows C (lowerSaddleGrid d m theta Cω x)
    (lowerSaddleD d m x) (lowerSaddleM m x) q Cfr lam
    (lowerAliasCutoff C.smoothness d m theta Cω
      (densityIntervalExponent C.densityLower C.densityUpper+1)
      (shrunkDensityExponent C.densityLower C.densityUpper) x)
    (lowerSaddleN C.smoothness d m theta Cω
      (shrunkDensityExponent C.densityLower C.densityUpper) x)
    (lowerSaddleMu d m theta Cω x)
def completeSourceSaddleActivity {d : ℕ} (C : ModelConstants d)
    (q : ℕ) (Cfr lam Cω x : ℝ) : ℝ :=
  highRowTotalMass (completeSourceSaddleRows C q Cfr lam Cω x).rowMass/highCenterMix C
def completeSourceSaddleActivityConstant {d : ℕ} (C : ModelConstants d)
    (q : ℕ) (Cfr lam : ℝ) : ℝ :=
  sourceSaddleActivityConstant d q C.densityLower C.densityUpper Cfr lam/highCenterMix C
theorem completeSourceSaddle_eta_eq {d : ℕ} (C : ModelConstants d) (Cω cf x : ℝ) :
    cf*(lowerSaddleGrid d (highCompleteSourceSaddleCoefficient C)
      (highCompleteSourceSaddleTheta C) Cω x : ℝ)^(-C.smoothness) =
      lowerSaddleEta C.smoothness d (highCompleteSourceSaddleCoefficient C)
        (highCompleteSourceSaddleTheta C) Cω cf x := by
  unfold lowerSaddleEta lowerSaddleH
  rw [Real.inv_rpow (lowerSaddleGrid_positive _ _ _ _ _).le,
    Real.rpow_neg (lowerSaddleGrid_positive _ _ _ _ _).le]
theorem eventually_completeSourceSaddle_parameters {d : ℕ} [NeZero d]
    (C : ModelConstants d) (hs : 1 < C.smoothness) (hd : 4*C.smoothness < (d : ℝ))
    {cf eta0 cm : ℝ} (_hcf : 0 < cf) (heta0 : 0 < eta0) (hcm : 0 < cm) (Cω : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      let m := highCompleteSourceSaddleCoefficient C
      let theta := highCompleteSourceSaddleTheta C
      let k := lowerSaddleGrid d m theta Cω x
      let M := lowerSaddleM m x
      let N := lowerSaddleN C.smoothness d m theta Cω
        (shrunkDensityExponent C.densityLower C.densityUpper) x
      let ell := lowerAliasCutoff C.smoothness d m theta Cω
        (densityIntervalExponent C.densityLower C.densityUpper+1)
        (shrunkDensityExponent C.densityLower C.densityUpper) x
      4 ≤ k ∧ 3 ≤ (lowerSaddleD d m x) ∧ highCenterResolutionThreshold C ≤ ↑M ∧
      0 < ell ∧ ell < N ∧ cf*↑k^(-C.smoothness) ≤ eta0 ∧
      8*highHistoryMassParameter d k C.densityLower C.densityUpper*x ≤ cm/↑M ∧
      1 ≤ lowerSaddleActivity C.smoothness d m theta Cω
        (shrunkDensityExponent C.densityLower C.densityUpper) x := by
  let m := highCompleteSourceSaddleCoefficient C
  let theta := highCompleteSourceSaddleTheta C
  let tau := densityIntervalExponent C.densityLower C.densityUpper
  have hab := C.densityLower_lt_one.trans C.one_lt_densityUpper
  have htau  := densityIntervalExponent_pos C.densityLower_pos hab
  have hm : 0 < m := lowerSaddleCoefficient_pos hs hd htau
  have htheta : 0 < theta := lowerSaddleTheta_pos hs hd htau
  have hd0 : (0 : ℝ) < d := by linarith
  obtain ⟨Ctau,_,hcontrol⟩ := exists_actual_lowerExponentControl C.densityLower_pos hab
  filter_upwards [(tendsto_natCast_atTop_iff.mp (lowerSaddleGrid_tendsto_atTop hd0 hm htheta Cω)).eventually (eventually_ge_atTop 4),
    (lowerSaddleM_tendsto_atTop hm).eventually
      (eventually_ge_atTop (max (highCenterResolutionThreshold C) 3)),
    (lowerSaddleN_tendsto_atTop hs hd hm htheta hcontrol Cω).eventually
      (eventually_ge_atTop ↑1),
    (lowerSaddleEta_tends_zero C.smoothness_pos hd0 hm htheta Cω cf).eventually
      (gt_mem_nhds heta0),
    eventually_highHistoryMass_saddle_guard (NeZero.pos d) hm htheta hcm Cω
      C.densityLower C.densityUpper hab,((lowerSaddleM_nat_tendsto_atTop hm).eventually hcontrol)] with x hk hM hN heta heps htauMx
  dsimp only
  have hM3 : (3 : ℝ) ≤ lowerSaddleM m x := (le_max_right _ _).trans hM
  have hD : 3 ≤ lowerSaddleD d m x := by
    have := Nat.le_ceil ((d+8)/4*(lowerSaddleM m x : ℝ))
    have hDr : (3 : ℝ) ≤ lowerSaddleD d m x := by
      dsimp only [lowerSaddleD] at ⊢
      nlinarith
    exact_mod_cast hDr
  have hDpos : (0 : ℝ) < lowerSaddleD d m x := by exact_mod_cast (by omega : 0 < lowerSaddleD d m x)
  have hcut : Real.exp (-(tau+1)*(lowerSaddleD d m x : ℝ)) < 1 := by
    apply Real.exp_lt_one_iff.mpr
    nlinarith
  have hellN : lowerAliasCutoff C.smoothness d m theta Cω (tau+1)
      (shrunkDensityExponent C.densityLower C.densityUpper) x <
      lowerSaddleN C.smoothness d m theta Cω
        (shrunkDensityExponent C.densityLower C.densityUpper) x := by
    unfold lowerAliasCutoff
    simpa only [mul_one] using mul_lt_mul_of_pos_left hcut (lowerSaddleN_positive _ _ _ _ _ _ _)
  exact ⟨hk,hD,(le_max_left _ _).trans hM,(by unfold lowerAliasCutoff; exact mul_pos (lowerSaddleN_positive _ _ _ _ _ _ _) (Real.exp_pos _)),hellN,
    (completeSourceSaddle_eta_eq C Cω cf x).trans_le heta.le,heps.2,(by unfold lowerSaddleActivity; exact one_le_mul_of_one_le_of_one_le (by nlinarith only [hN]) (by apply Real.one_le_exp_iff.mpr; exact mul_nonneg (htau.le.trans htauMx.1) (Nat.cast_nonneg _)))⟩
end
def lowerSaddleFineFieldScale (s d m theta C c0 : ℝ) (tauM : ℕ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (2 * tauM (lowerSaddleM m x) * lowerSaddleM m x) *
    lowerSaddleN s d m theta C tauM x ^ (4 - d) *
    Real.exp (c0 * (2 * d - 4) * lowerSaddleD d m x)
theorem fine_field_scale_absorption {d N mu ell tau M D c0 : ℝ}
    (hN : 0 < N) (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1)
    (hell : ell = N * Real.exp (-c0 * D))
    (hscale : Real.exp (2 * tau * M) * N ^ (4 - d) *
      Real.exp (c0 * (2 * d - 4) * D) ≤ 1) :
    Real.exp (2 * tau * M) * mu ^ 4 * ell ^ (4 - 2 * d) ≤
      mu ^ 2 * N ^ (-d) := by
  have hNpow : N ^ (-d) * N ^ (4 - d) = N ^ (4 - 2 * d) := by
    rw [← Real.rpow_add hN]
    congr 1
    ring
  have he : Real.exp (-c0 * D) ^ (4 - 2 * d) = Real.exp (c0 * (2 * d - 4) * D) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  rw [hell, Real.mul_rpow hN.le (Real.exp_pos _).le, he]
  have hmu2 : mu ^ 2 ≤ 1 := pow_le_one₀ hmu hmu1
  have h := mul_le_mul hmu2 hscale (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
  calc
    _ = (mu ^ 2 * N ^ (-d)) * (mu ^ 2 *
        (Real.exp (2 * tau * M) * N ^ (4 - d) * Real.exp (c0 * (2 * d - 4) * D))) := by
      rw [show (mu ^ 2 * N ^ (-d)) * (mu ^ 2 *
          (Real.exp (2 * tau * M) * N ^ (4 - d) * Real.exp (c0 * (2 * d - 4) * D))) =
        mu ^ 4 * Real.exp (2 * tau * M) * (N ^ (-d) * N ^ (4 - d)) *
          Real.exp (c0 * (2 * d - 4) * D) by ring, hNpow]
      ring
    _ ≤ (mu ^ 2 * N ^ (-d)) * 1 := mul_le_mul_of_nonneg_left (by simpa only [one_mul] using h) (by positivity)
    _ = _ := mul_one _
theorem eventually_lowerSaddle_fine_field_energy_scale {s d m theta tau Ctau : ℝ}
    {tauM : ℕ → ℝ} (hs : 1 < s) (hd : 4 * s < d) (hm : 0 < m) (htheta : 0 < theta)
    (hcontrol : LowerExponentControl tauM tau Ctau) (C c0 ) :
    ∀ᶠ x : ℝ in atTop,
      Real.exp (2 * tauM (lowerSaddleM m x) * lowerSaddleM m x) *
        lowerSaddleMu d m theta C x ^ 4 *
        lowerAliasCutoff s d m theta C c0 tauM x ^ (4 - 2 * d) ≤
          lowerSaddleMu d m theta C x ^ 2 * lowerSaddleN s d m theta C tauM x ^ (-d) := by
  have hd0 : 0 < d := by linarith only [hs, hd]
  have h_lowerSaddleFineFieldScale_tends_zero : Tendsto (lowerSaddleFineFieldScale s d m theta C c0 tauM) atTop (𝓝 0) := by
    have hd0 : 0 < d := by linarith only [hs, hd]
    have hd4 : 4 < d := by linarith only [hs, hd]
    have hM := lowerSaddleM_tendsto_atTop hm
    have hM2 : Tendsto (fun x : ℝ => (lowerSaddleM m x : ℝ) ^ 2) atTop atTop :=
      (tendsto_pow_atTop (by decide : ↑2 ≠ 0)).comp hM
    have htau := ((lowerSaddleTau_limit hm hcontrol).mul hM.inv_tendsto_atTop).const_mul 2
    have hN := (lowerSaddleLogN_div_M_sq_limit hd0 hm htheta hcontrol s C).const_mul (4 - d)
    have hD := (lowerSaddleD_div_M_sq_tends_zero hd0 hm).const_mul (c0 * (2 * d - 4))
    have hh := (htau.add hN).add hD
    simp only [mul_zero, zero_add, add_zero] at hh
    have h_lowerSaddleFineFieldScale_positive (x : ℝ) : 0 < lowerSaddleFineFieldScale s d m theta C c0 tauM x := by
      unfold lowerSaddleFineFieldScale
      positivity [lowerSaddleN_positive s d m theta C tauM x]
    apply positive_profile_tends_zero_of_log_div_negative
      (c := (4 - d) * (((d - 4 * s) / (d * (d + 4))) / m ^ 2)) hM2
      (by have hp : 0 < ((d - 4 * s) / (d * (d + 4))) / m ^ 2 := by positivity
          exact mul_neg_of_neg_of_pos (by linarith only [hd4]) hp)
      (Filter.Eventually.of_forall h_lowerSaddleFineFieldScale_positive)
    refine hh.congr' ?_
    filter_upwards [hM.eventually (eventually_gt_atTop 0)] with x hMx
    unfold lowerSaddleFineFieldScale
    have hNp := lowerSaddleN_positive s d m theta C tauM x
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne',
      Real.log_mul (Real.exp_pos _).ne' (Real.rpow_pos_of_pos hNp _).ne',
      Real.log_exp, Real.log_exp, Real.log_rpow hNp]
    simp only [Pi.inv_apply]
    field_simp [hMx.ne']
  filter_upwards [h_lowerSaddleFineFieldScale_tends_zero.eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    (lowerSaddleMu_tends_zero hd0 hm htheta C).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop (0 : ℝ)] with x hscale hmu hx
  apply fine_field_scale_absorption (lowerSaddleN_positive s d m theta C tauM x)
    (mul_nonneg hx.le (Real.rpow_pos_of_pos (lowerSaddleH_positive d m theta C x) _).le) hmu.le rfl
  exact hscale.le
theorem lowerSaddleD_le_fixed_multiple  (hd : 0 ≤ d)
    (hM : 1 ≤ (lowerSaddleM m x : ℝ)) :
    (lowerSaddleD d m x ) ≤ ((d+8)/4+1)*(lowerSaddleM m x ) := by
  have h := Nat.ceil_lt_add_one
    (mul_nonneg (by positivity : 0 ≤ (d+8)/4) (Nat.cast_nonneg (lowerSaddleM m x)))
  change (lowerSaddleD d m x ) < (d+8)/4*(lowerSaddleM m x )+1 at h
  nlinarith only [h,hM]
abbrev completeSaddleM {d : ℕ} (C : ModelConstants d) (x : ℝ) :=
  lowerSaddleM (highCompleteSourceSaddleCoefficient C) x
abbrev completeSaddleD {d : ℕ} (C : ModelConstants d) (x : ℝ) :=
  lowerSaddleD d (highCompleteSourceSaddleCoefficient C) x
abbrev completeSaddleN {d : ℕ} (C : ModelConstants d) (Cω x : ℝ) :=
  lowerSaddleN C.smoothness d (highCompleteSourceSaddleCoefficient C)
    (highCompleteSourceSaddleTheta C) Cω (shrunkDensityExponent C.densityLower C.densityUpper) x
abbrev completeSaddleMu {d : ℕ} (C : ModelConstants d) (Cω x : ℝ) :=
  lowerSaddleMu d (highCompleteSourceSaddleCoefficient C) (highCompleteSourceSaddleTheta C) Cω x
abbrev completeSaddleEta {d : ℕ} (C : ModelConstants d) (Cω cf x : ℝ) :=
  lowerSaddleEta C.smoothness d (highCompleteSourceSaddleCoefficient C)
    (highCompleteSourceSaddleTheta C) Cω cf x
abbrev completeSaddleC0 {d : ℕ} (C : ModelConstants d) :=
  densityIntervalExponent C.densityLower C.densityUpper+1
abbrev completeSaddleEll {d : ℕ} (C : ModelConstants d) (Cω x : ℝ) :=
  lowerAliasCutoff C.smoothness d (highCompleteSourceSaddleCoefficient C)
    (highCompleteSourceSaddleTheta C) Cω (completeSaddleC0 C)
    (shrunkDensityExponent C.densityLower C.densityUpper) x
abbrev completeSaddleTau {d : ℕ} (C : ModelConstants d) (x : ℝ) :=
  shrunkDensityExponent C.densityLower C.densityUpper (completeSaddleM C x)
abbrev completeSaddleAD {d : ℕ} (C : ModelConstants d) (x : ℝ) :=
  C.densityLower+1/(completeSaddleM C x )
abbrev completeSaddleBD {d : ℕ} (C : ModelConstants d) (x : ℝ) :=
  C.densityUpper-1/(completeSaddleM C x )
structure CompleteSaddleEnergyGuards {d : ℕ} (C : ModelConstants d) (Cω cf x : ℝ) : Prop where
  resolution : highCenterResolutionThreshold C ≤ (completeSaddleM C x : ℝ)
  N_one : 1 ≤ completeSaddleN C Cω x
  mu_positive : 0 < completeSaddleMu C Cω x
  mu_one : completeSaddleMu C Cω x ≤ 1
  mu_log : completeSaddleMu C Cω x*(1+Real.log (completeSaddleN C Cω x)) ≤ 1
  response_taylor : (completeSaddleEta C Cω cf x)^(4*lowerSaddleResponseOrder C.smoothness d)*
    (completeSaddleN C Cω x)^d ≤ 1
  tau_nonneg : 0 ≤ completeSaddleTau C x
  tau_le : completeSaddleTau C x ≤ completeSaddleC0 C
  degree_multiple : (completeSaddleD C x : ℝ) ≤
    (((d : ℝ)+8)/4+1)*(completeSaddleM C x : ℝ)
  ell_one : 1 ≤ completeSaddleEll C Cω x
  ell_lt_N : completeSaddleEll C Cω x < completeSaddleN C Cω x
  field_scale_square : Real.exp (2*completeSaddleTau C x*(completeSaddleM C x : ℝ))*
    (completeSaddleMu C Cω x)^4*((completeSaddleEll C Cω x)^(2-(d : ℝ)))^2 ≤
      (completeSaddleMu C Cω x)^2*(completeSaddleN C Cω x)^(-(d : ℝ))
  bd_nonneg : 0 ≤ completeSaddleBD C x
  bd_le : completeSaddleBD C x ≤ C.densityUpper
  ad_positive : 0 < completeSaddleAD C x
  density_interval : completeSaddleAD C x < completeSaddleBD C x
 theorem eventually_completeSaddleEnergyGuards  [NeZero d]
    (C : ModelConstants d) (hs : 1 < C.smoothness) (hd : 4*C.smoothness < (d : ℝ))
     (hcf : 0 < cf) (Cω ) :
    ∀ᶠ n : ℕ in atTop, CompleteSaddleEnergyGuards C Cω cf n := by
  let m := highCompleteSourceSaddleCoefficient C
  let theta := highCompleteSourceSaddleTheta C
  let tau := densityIntervalExponent C.densityLower C.densityUpper
  have hab := C.densityLower_lt_one.trans C.one_lt_densityUpper
  have htau : 0 < tau := densityIntervalExponent_pos C.densityLower_pos hab
  have hm : 0 < m := lowerSaddleCoefficient_pos hs hd htau
  obtain ⟨Ctau,_,hcontrol⟩ := exists_actual_lowerExponentControl C.densityLower_pos hab
  obtain ⟨K,_,h⟩ := actual_lowerSaddle_fixed_regime_window hs hd C.densityLower_pos
    hab hcf
  have hhier := actual_lowerAlias_hierarchy (Cact := 1) (Cs := 1) hs hd
    C.densityLower_pos hab (by norm_num) (by norm_num) Cω
  have hparams := eventually_completeSourceSaddle_parameters C hs hd hcf
    (by norm_num : (0 : ℝ)<1) (by norm_num : (0 : ℝ)<1) Cω
  filter_upwards [tendsto_natCast_atTop_atTop.eventually (h Cω 1 0 (by norm_num)),
    tendsto_natCast_atTop_atTop.eventually hhier,
    tendsto_natCast_atTop_atTop.eventually (eventually_lowerSaddle_fine_field_energy_scale hs hd hm (lowerSaddleTheta_pos hs hd htau) hcontrol Cω (tau+1)),
    tendsto_natCast_atTop_atTop.eventually hparams,
    tendsto_natCast_atTop_atTop.eventually
      ((lowerSaddleM_tendsto_atTop hm).eventually (eventually_ge_atTop 1))]
    with n hregn hhiern hscalen hpn hMone
  change LowerSaddleReg K 1 C.smoothness d m theta Cω cf 0
    (shrunkDensityExponent C.densityLower C.densityUpper) n at hregn
  rcases hregn with ⟨_,_,hN,hmu,hmu1,_,_,_,_,_,_,hqt⟩
  change LowerAliasHierarchy C.smoothness d m theta Cω 1 1 (tau+1)
    (shrunkDensityExponent C.densityLower C.densityUpper) n at hhiern
  rcases hhiern with ⟨hell,htaule,hmulog,_,_,_,_,_,_,_,_,_⟩
  dsimp only at hpn
  obtain ⟨had,hadb⟩ := high_source_interval_numeric C (completeSaddleM C n ) hpn.2.2.1
  have hsquare : ((completeSaddleEll C Cω n)^(2-(d : ℝ)))^2 =
      (completeSaddleEll C Cω n)^(4-2*(d : ℝ)) := by
    rw [← Real.rpow_mul_natCast (by linarith only [hell] : 0 ≤ completeSaddleEll C Cω n)]
    congr 1
    ring
  refine ⟨hpn.2.2.1,hN,hmu,hmu1.le,hmulog,?_,((densityIntervalExponent_pos (by simpa only [one_div] using had) (by simpa only [one_div] using hadb)).le),htaule,
    lowerSaddleD_le_fixed_multiple (Nat.cast_nonneg _) hMone,hell.le,hpn.2.2.2.2.1,
    ?_,had.le.trans hadb.le,?_,had,hadb⟩
  · simpa only [lowerSaddleResponseQuantity,Real.rpow_natCast] using hqt
  · rw [hsquare]
    exact hscalen
  · dsimp only [completeSaddleBD]
    exact sub_le_self _ (one_div_nonneg.mpr (Nat.cast_nonneg _))
end NearlyMinimax
