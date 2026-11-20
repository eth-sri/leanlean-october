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

variable {Ω Z : Type*}

theorem normalized_likelihood_score_square_transfer [MeasurableSpace Z]
    (μ : Measure Z) {c : ℝ} (hc : 0 < c) {L : Z → ℝ} (D : Z → ℝ)
    (hL : Measurable L) (hpos : ∀ z, 0 < L z) :
    (Integrable (fun z => (D z / L z) ^ 2)
      (μ.withDensity (fun z => ENNReal.ofReal (L z / c))) ↔
        Integrable (fun z => D z ^ 2 / L z) μ) ∧
    (∫ z, (D z / L z) ^ 2 ∂μ.withDensity (fun z => ENNReal.ofReal (L z / c))) =
      c⁻¹ * ∫ z, D z ^ 2 / L z ∂μ := by
  have hf : Measurable (fun z => ENNReal.ofReal (L z / c)) :=
    ENNReal.measurable_ofReal.comp (hL.div_const c)
  have he z : (ENNReal.ofReal (L z / c)).toReal * (D z / L z) ^ 2 =
      c⁻¹ * (D z ^ 2 / L z) := by
    rw [ENNReal.toReal_ofReal (div_nonneg (hpos z).le hc.le)]
    field_simp <;> ring
  constructor
  · rw [integrable_withDensity_iff_integrable_smul' hf
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simp [he]
    exact integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (inv_ne_zero hc.ne')) _
  · have hi := integral_withDensity_eq_integral_toReal_smul (μ := μ) hf
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) (fun z => (D z / L z) ^ 2)
    change _ =
      ∫ z, (ENNReal.ofReal (L z / c)).toReal * (D z / L z) ^ 2 ∂μ at hi
    rw [hi]
    simp_rw [he]
    exact integral_const_mul _ _

theorem raw_joint_fisher_integrable_bound
    [MeasurableSpace Ω] [MeasurableSpace Z]
    {ν : Measure Ω} [IsFiniteMeasure ν] (μ : Measure Z) [SFinite μ]
    {c : Ω → ℝ} (hc : ∀ ω, 0 < c ω) (hci : Integrable c ν)
    {L D : Ω → Z → ℝ} (hL : Measurable (Function.uncurry L))
    (hD : Measurable (Function.uncurry D)) (hpos : ∀ ω z, 0 < L ω z)
    {B : ℝ} (hB : 0 ≤ B)
    (hscore : ∀ ω, Integrable (fun z => (D ω z / L ω z) ^ 2)
      (μ.withDensity (fun z => ENNReal.ofReal (L ω z / c ω))))
    (hbound : ∀ ω, (∫ z, (D ω z / L ω z) ^ 2
      ∂μ.withDensity (fun z => ENNReal.ofReal (L ω z / c ω))) ≤ B) :
    Integrable (fun z => D z.1 z.2 ^ 2 / L z.1 z.2) (ν.prod μ) ∧
    (∫ z, D z.1 z.2 ^ 2 / L z.1 z.2 ∂ν.prod μ) ≤ (∫ ω, c ω ∂ν) * B := by
  let W : Ω × Z → ℝ := fun z => D z.1 z.2 ^ 2 / L z.1 z.2
  have hW  := (hD.pow_const 2).div hL
  have hWi ω  :=
    (normalized_likelihood_score_square_transfer μ (hc ω) (D ω)
      hL.of_uncurry_left (hpos ω)).1.mp (hscore ω)
  have hWn ω z : 0 ≤ W (ω, z) := div_nonneg (sq_nonneg _) (hpos ω z).le
  have he ω : (∫ z, W (ω, z) ∂μ) = c ω *
      (∫ z, (D ω z / L ω z) ^ 2 ∂μ.withDensity (fun z => ENNReal.ofReal (L ω z / c ω))) := by
    grind [(normalized_likelihood_score_square_transfer μ (hc ω) (D ω) hL.of_uncurry_left (hpos ω)).2]
  have hnorm ω : (∫ z, ‖W (ω, z)‖ ∂μ) ≤ c ω * B := by
    have heNorm : (fun z => ‖W (ω, z)‖) = (fun z => W (ω, z)) := by
      funext z
      simp_all
    simp_all
  have hnormI : Integrable (fun ω => ∫ z, ‖W (ω, z)‖ ∂μ) ν := by
    apply (hci.mul_const B).mono' hW.stronglyMeasurable.norm.integral_prod_right'.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    exact hnorm ω
  have hWI : Integrable W (ν.prod μ) :=
    (integrable_prod_iff hW.aestronglyMeasurable).mpr
      ⟨Filter.Eventually.of_forall hWi, hnormI⟩
  refine ⟨hWI, ?_⟩
  rw [integral_prod _ hWI]
  calc
    _ ≤ _ := by
      apply integral_mono_ae hWI.integral_prod_left (hci.mul_const B)
      apply Filter.Eventually.of_forall
      simp_all
    _ = _ := integral_mul_const _ _

theorem high_raw_joint_fisher_integrable_bound [MeasurableSpace Ω]
    {d : ℕ} (ν : Measure Ω) [IsProbabilityMeasure ν] {n : ℕ} (a V : ℝ)
    {p F : Ω → Covariate d → ℝ}
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    {aRaw bRaw : ℝ} (haRaw : 0 < aRaw)
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ ω x y, 0 < ternaryMass a (F ω x) V y)
    {D : Ω → (IndexedSample d n) → ℝ}
    (hD : Measurable (Function.uncurry D)) {B : ℝ} (hB : 0 ≤ B)
    (hscore : ∀ ω, Integrable (fun z => (D ω z / highRawSampleLikelihood a V (p ω) (F ω) z) ^ 2)
      (highSampleIndexKernel n a V hp hF ω))
    (hbound : ∀ ω, (∫ z, (D ω z / highRawSampleLikelihood a V (p ω) (F ω) z) ^ 2
      ∂highSampleIndexKernel n a V hp hF ω) ≤ B) :
    Integrable (fun z => D z.1 z.2 ^ 2 / highRawSampleLikelihood a V (p z.1) (F z.1) z.2)
      (ν.prod (highSampleReference d n)) ∧
    (∫ z, D z.1 z.2 ^ 2 / highRawSampleLikelihood a V (p z.1) (F z.1) z.2
      ∂ν.prod (highSampleReference d n)) ≤
      massPowerNormalizer ν (fun ω => highRawDensityMass (p ω)) n * B := by
  let c  := fun ω => highRawDensityMass (p ω) ^ n
  have hmBound ω  :=
    highRawDensityMass_mem_Icc hp.of_uncurry_left haRaw
      (Filter.Eventually.of_forall (hraw ω))
  have hm ω  := haRaw.trans_le (hmBound ω).1
  have hc  := fun ω => pow_pos (hm ω) n
  have hci : Integrable c ν := by
    apply (integrable_const (bRaw ^ n)).mono' ((highRawDensityMass_joint_measurable hp).pow_const n).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hc ω).le]
    exact pow_le_pow_left₀ (hm ω).le (hmBound ω).2 n
  have he ω : highSampleIndexKernel n a V hp hF ω =
      (highSampleReference d n).withDensity (fun z =>
        ENNReal.ofReal (highRawSampleLikelihood a V (p ω) (F ω) z / c ω)) := by
    rw [highSampleIndexKernel_apply]
    congr 1
    funext z
    congr 1
    apply (eq_div_iff (hc ω).ne').mpr
    simpa only [ mul_comm] using
      highSampleLikelihood_mass_cancellation n a V (F ω) (hm ω).ne' z
  exact raw_joint_fisher_integrable_bound (highSampleReference d n) hc hci
    (L := (fun ω => highRawSampleLikelihood a V (p ω) (F ω)))
    (highRawSampleLikelihood_joint_measurable n a V hp hF) hD
    (fun ω z => Finset.prod_pos (fun i _ => mul_pos
      (haRaw.trans_le (hraw ω (z.1 i)).1) (hq ω _ _))) hB
    (fun ω => by rw [← he ω]; exact hscore ω)
    (fun ω => by rw [← he ω]; exact hbound ω)

end NearlyMinimax
