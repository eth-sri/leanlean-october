module

public import NearlyMinimax.HighMassTilt
public import NearlyMinimax.HighSelectedScoreEnergy

@[expose] public section

/-! Exact raw-likelihood Fisher transfer. Integrability under the genuine
normalized experiment yields integrability of D²/L under the fixed raw
reference, and a uniform conditional budget survives mass-power tilting. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private theorem raw_joint_fisher_integrable_bound {Ω Z : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Z]
    (ν : Measure Ω) (μ : Measure Z) [SFinite ν] [SFinite μ]
    (c : Ω → ℝ) (hc : ∀ ω, 0 < c ω) (hci : Integrable c ν)
    (L D : Ω → Z → ℝ) (hL : Measurable (Function.uncurry L))
    (hD : Measurable (Function.uncurry D)) (hpos : ∀ ω z, 0 < L ω z)
    (B : ℝ) (hscore : ∀ ω,
      let μω := μ.withDensity (fun z => ENNReal.ofReal (L ω z / c ω))
      let S := fun z => (D ω z / L ω z) ^ 2
      Integrable S μω ∧ (∫ z, S z ∂μω) ≤ B) :
    Integrable (fun z : Ω × Z => D z.1 z.2 ^ 2 / L z.1 z.2) (ν.prod μ) ∧
    (∫ z : Ω × Z, D z.1 z.2 ^ 2 / L z.1 z.2 ∂ν.prod μ) ≤ (∫ ω, c ω ∂ν) * B := by
  have hloc (ω : Ω) := hscore ω
  have he (ω : Ω) (z : Z) : (L ω z / c ω) * (D ω z / L ω z) ^ 2 =
      (c ω)⁻¹ * (D ω z ^ 2 / L ω z) := by field_simp [(hpos ω z).ne']
  have hi (ω : Ω) := (hloc ω).1
  have hb (ω : Ω) := (hloc ω).2
  dsimp only at hi hb
  simp_rw [integrable_realDensity_iff (hL.of_uncurry_left.div_const _)
    (fun z => div_nonneg (hpos _ z).le (hc _).le), he,
    integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (inv_ne_zero (hc _).ne'))] at hi
  simp_rw [integral_realDensity (hL.of_uncurry_left.div_const _)
    (fun z => div_nonneg (hpos _ z).le (hc _).le), he, integral_const_mul,
    ← div_eq_inv_mul, div_le_iff₀ (hc _), mul_comm B] at hb
  rw [← integral_mul_const]
  exact integral_prod_nonneg_domination ((hD.pow_const 2).div hL)
    (fun z => div_nonneg (sq_nonneg _) (hpos z.1 z.2).le) (hci.mul_const B) hb hi

/-- Latent Fisher energy under the normalized, mass-power tilted experiment,
expressed using its raw likelihood and a fixed reference measure. -/
def HighRawFisherBudget {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (ν : Measure Ω) (n : ℕ) (a V : ℝ) (p F : Ω → Covariate d → ℝ)
    (D : Ω → TernarySample d n → ℝ) (B : ℝ) : Prop :=
  let W := fun z : Ω × TernarySample d n =>
    D z.1 z.2 ^ 2 / highRawSampleLikelihood n a V (p z.1) (F z.1) z.2
  let μ := ν.prod (highSampleReference d n)
  Integrable W μ ∧ (massPowerNormalizer ν (fun ω => highRawDensityMass (p ω)) n)⁻¹ *
    (∫ z, W z ∂μ) ≤ B

theorem high_raw_joint_fisher_integrable_bound {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (ν : Measure Ω) [IsProbabilityMeasure ν] (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (aRaw bRaw : ℝ) (haRaw : 0 < aRaw)
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ ω x y, 0 < ternaryMass a (F ω x) V y)
    (D : Ω → TernarySample d n → ℝ)
    (hD : Measurable (Function.uncurry D)) (B : ℝ)
    (hscore : ∀ ω,
      let μω := highSampleIndexKernel n a V p F hp hF ω
      let S := fun z => (D ω z / highRawSampleLikelihood n a V (p ω) (F ω) z) ^ 2
      Integrable S μω ∧ (∫ z, S z ∂μω) ≤ B) :
    HighRawFisherBudget ν n a V p F D B := by
  let c : Ω → ℝ := fun ω => highRawDensityMass (p ω) ^ n
  have hmBound (ω : Ω) : aRaw ≤ highRawDensityMass (p ω) ∧ highRawDensityMass (p ω) ≤ bRaw :=
    highRawDensityMass_joint_mem_Icc hp haRaw hraw ω
  have hm (ω : Ω) : 0 < highRawDensityMass (p ω) := haRaw.trans_le (hmBound ω).1
  have hc : ∀ ω, 0 < c ω := fun ω => pow_pos (hm ω) n
  have hci : Integrable c ν := massPower_integrable ν _
    (highRawDensityMass_joint_measurable p hp) n aRaw bRaw haRaw hmBound
  have he (ω : Ω) : highSampleIndexKernel n a V p F hp hF ω =
      (highSampleReference d n).withDensity (fun z =>
        ENNReal.ofReal (highRawSampleLikelihood n a V (p ω) (F ω) z / c ω)) :=
    highSampleIndexKernel_apply n a V p F hp hF ω
  have hj := raw_joint_fisher_integrable_bound ν (highSampleReference d n) c hc hci
    (fun ω => highRawSampleLikelihood n a V (p ω) (F ω)) D
    (highRawSampleLikelihood_joint_measurable n a V p F hp hF) hD
    (fun ω z => Finset.prod_pos (fun i _ => mul_pos
      (haRaw.trans_le (hraw ω (z.1 i)).1) (hq ω _ _))) B
    (fun ω => he ω ▸ hscore ω)
  have hG := massPowerNormalizer_pos ν _ (highRawDensityMass_joint_measurable p hp) n
    aRaw bRaw haRaw hmBound
  unfold HighRawFisherBudget
  refine ⟨hj.1, ?_⟩
  rw [← div_eq_inv_mul, div_le_iff₀ hG, mul_comm B]
  exact hj.2

end NearlyMinimax
