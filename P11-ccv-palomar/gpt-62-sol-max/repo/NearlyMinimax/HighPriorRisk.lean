module

public import NearlyMinimax.HighScoreTimeKernel
public import NearlyMinimax.PaperScorePath


@[expose] public section

/-! The source marked-history prior, its genuine normalized observation law,
and its observed posterior score imply the manuscript's path-risk comparison.
The analytical score assumptions are proved from the actual likelihood. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
variable {J : Type*} [Fintype J] [LinearOrder J]
attribute [local irreducible] highMarginalRealScore highRealSampleKernel historyMarkedPrior
  massPowerTilt massPowerNormalizer highRawDensityMass

theorem historyMarkedPrior_original_minimax_path_bound
    {dependent : J → J → Prop} {Δ : ℕ} {T Ba : ℝ}
    {E : Type*} [MeasurableSpace E] [StandardBorelSpace E]
    {π : Measure E} [IsProbabilityMeasure π] {activation : E → ℝ}
    (prior : HistoryPriorBounds dependent Δ π activation T Ba) (hT : 0 ≤ T)
    {d : ℕ} (C : ModelConstants d) (n : ℕ) (a v η aRaw bRaw M ε : ℝ)
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
    (hE : ∀ t ∈ Icc 0 T, HighRawFisherBudget (historyMarkedPrior dependent Δ t π activation)
      n a (v-η^2*t) p F (highHistoryLikelihoodDerivative dependent prior.symm π activation n a (v-η^2*t) η p F) M) :
    ENNReal.ofReal (η^4*T^2 / (2 + T * Real.sqrt M)^2 -
      (effectiveVarianceUpper C-C.varianceLower)^2*ε) ≤ minimaxRisk C n := by
  let ν (t : ℝ) := historyMarkedPrior dependent Δ t π activation
  let σ (t : ℝ) := massPowerTilt (ν t) (fun ω => highRawDensityMass (p ω)) n
  let L (t : ℝ) := highRealSampleKernel n a (v-η^2*t) p F hp hF
  let R (t : ℝ) := highMarginalRealScore dependent prior.symm (ν t) π activation n a (v-η^2*t) η p F
  let _ := prior.reference_probability
  have hν (t : ℝ) (ht : t ∈ Icc 0 T) := prior.probability ht
  have hσ (t : ℝ) (ht : t ∈ Icc 0 T) : IsProbabilityMeasure (σ t) := by
    let _ := hν t ht
    exact massPowerTilt_isProbability (ν t) _ (highRawDensityMass_joint_measurable p hp)
      n aRaw bRaw haRaw (fun ω => highRawDensityMass_joint_mem_Icc hp haRaw hraw ω)
  have hL (t : ℝ) (ht : t ∈ Icc 0 T) : IsMarkovKernel (L t) :=
    highRealSampleKernel_markov n a (v-η^2*t) p F hp hF aRaw bRaw haRaw hraw ha.ne'
      (fun ω x y => (hq t ht ω x y).le)
  have hsample (t : ℝ) (ht : t ∈ Icc 0 T) (ω) : L t ω = sampleLaw (θ t ω) n := by
    rw [hθ t ht ω]
    apply highRealSampleKernel_eq_sampleLaw <;> assumption
  have hvariance (t : ℝ) (ht : t ∈ Icc 0 T) (ω) : (θ t ω).variance = v-η^2*t := by
    rw [hθ t ht ω]
    rfl
  have hfisher (t : ℝ) (ht : t ∈ Icc 0 T) := by
    let _ := hν t ht
    exact highMarginalRealScore_memLp_energy dependent prior.symm (ν t) π activation prior.measurable
      Ba prior.bound_nonneg prior.bound n a (v-η^2*t) η aRaw bRaw ha haRaw p F hp hF hraw (hq t ht) M (hE t ht)
  have hR : ∀ᵐ t ∂volume, t ∈ Icc 0 T → MemLp (R t) 2 (L t ∘ₘ σ t) :=
    .of_forall fun t ht => (hfisher t ht).1
  have hc := historyMarkedPrior_dataScore_centered_ae prior n a v η aRaw bRaw ha haRaw p F hp hF hraw hmass hq
  have hB : 0 ≤ effectiveVarianceUpper C :=
    C.varianceLower_pos.le.trans (effective_variance_interval_nondegenerate C).le
  have hreg (S : BoundedEstimator C n) :=
    historyMarkedPrior_dataMean_regularity prior n a v η aRaw bRaw ha haRaw p F hp hF hraw
      hmass S.val.val S.val.property (effectiveVarianceUpper C) hB (S.abs_le C) hq hT
  let W (t : ℝ) := ∫ z, (R t z)^2 ∂(L t ∘ₘ σ t)
  have hW (t : ℝ) (ht : t ∈ Icc 0 T) : W t ≤ M :=
    (hfisher t ht).2
  have hi := highHistoryScore_sqrt_energy_intervalIntegrable prior n a v η aRaw bRaw ha haRaw hT
    p F hp hF hraw (fun t ht ω x y => (hq t ht ω x y).le) M hW
  have hh := paper_score_to_risk C σ L θ (fun t => v-η^2*t) R T ε hT hσ hL hsample hvariance
    hV bad hbad hlegal hbadmass hR hc (fun S => (hreg S).1) (fun S => time_ae_of_Ioo (hreg S).2) hi
  have he : ((v-η^2*T)-(v-η^2*0))^2 = η^4*T^2 := by ring
  rw [he] at hh
  have hbound := intervalIntegral.integral_mono_on hT hi (intervalIntegrable_const (c := Real.sqrt M))
    (fun t ht => Real.sqrt_le_sqrt (hW t ht))
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hbound
  have h0 : 0 ≤ ∫ t in 0..T, Real.sqrt (W t) :=
    intervalIntegral.integral_nonneg hT (fun _ _ => Real.sqrt_nonneg _)
  refine le_trans (ENNReal.ofReal_le_ofReal (sub_le_sub_right ?_ _)) hh
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  gcongr

end NearlyMinimax
