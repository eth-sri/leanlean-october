module

public import NearlyMinimax.HighLikelihoodDerivative


@[expose] public section

/-! Actual raw data observables and the mass-tilted original observation mean. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω]

section
variable {d n : ℕ} (a V : ℝ) (p F : Covariate d → ℝ) (H : (Fin n → Observation d) → ℝ)

def highRawObservable : ℝ :=
  ∫ z, H (encodeDesignResponse a z) * highRawSampleLikelihood a V p F z
    ∂highSampleReference d n

def highRawObservableVarianceDerivative : ℝ :=
  ∫ z, H (encodeDesignResponse a z) * highRawSampleVarianceDerivative a V p F z
    ∂highSampleReference d n

end

section
variable {d n : ℕ} (a V : ℝ) {p F : Ω → Covariate d → ℝ} (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) {H : (Fin n → Observation d) → ℝ} (hH : Measurable H)
include hF hH hp

theorem highRawObservable_measurable : Measurable (fun ω => highRawObservable a V (p ω) (F ω) H) := by
  have h  :=
    ((hH.comp (encodeDesignResponse_measurable a)).comp measurable_snd).mul
      (highRawSampleLikelihood_joint_measurable n a V hp hF)
  exact h.stronglyMeasurable.integral_prod_right'.measurable

end

variable {d : ℕ} (ν : Measure Ω) {n : ℕ} {a V P B : ℝ} (ha : 0 < a) (hP : 0 ≤ P) (hB : 0 ≤ B)
    {p F : Covariate d → ℝ} (hp : ∀ x, |p x| ≤ P)

include hP hB hp in
theorem highRawObservable_abs_le (ha : a ≠ 0)
    (hq : ∀ x y, 0 ≤ ternaryMass a (F x) V y)
    {H : (Fin n → Observation d) → ℝ} (hHb : ∀ z, |H z| ≤ B) :
    |highRawObservable a V p F H| ≤ B * P ^ n * (highSampleReference d n).real Set.univ := by
  rw [highRawObservable, ← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le_const
  exact Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs, abs_mul]
    bound [highRawSampleLikelihood_abs_le hP hp ha hq z]

include ha hP hB hp in
theorem highRawObservableVarianceDerivative_abs_le
    (hq : ∀ x y, 0 ≤ ternaryMass a (F x) V y)
    {H : (Fin n → Observation d) → ℝ} (hHb : ∀ z, |H z| ≤ B) :
    |highRawObservableVarianceDerivative a V p F H| ≤
      B * (P ^ n * (n / a ^ 2)) * (highSampleReference d n).real Set.univ := by
  rw [highRawObservableVarianceDerivative, ← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le_const
  exact Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs, abs_mul]
    bound [highRawSampleVarianceDerivative_abs_le ha hP hp hq z]

/-- The actual original real-data mean under the genuine mass tilt equals
G_n^-1 times the raw-likelihood observable mean. -/
theorem massPowerTilt_highReal_observable_mean [IsProbabilityMeasure ν]
    {n : ℕ} {a V : ℝ} {p F : Ω → Covariate d → ℝ}
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    {aRaw bRaw : ℝ} (haRaw : 0 < aRaw)
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw) (ha : a ≠ 0)
    (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) V y)
    {H : (Fin n → Observation d) → ℝ} (hH : Measurable H)
    {B : ℝ} (hB : 0 ≤ B) (hHb : ∀ z, |H z| ≤ B) :
    (∫ ω, ∫ z, H z ∂highRealSampleKernel n a V hp hF ω
      ∂massPowerTilt ν (fun ω => highRawDensityMass (p ω)) n) =
      (massPowerNormalizer ν (fun ω => highRawDensityMass (p ω)) n)⁻¹ *
        ∫ ω, highRawObservable a V (p ω) (F ω) H ∂ν := by
  have hbound ω  :=
    highRawDensityMass_mem_Icc hp.of_uncurry_left haRaw
      (Eventually.of_forall (hraw ω))
  let _ := massPowerTilt_isProbability ν (highRawDensityMass_joint_measurable hp) n haRaw hbound
  let _ := highSampleIndexKernel_markov n hp hF haRaw hraw ha hq
  have hM : Measurable (fun z : Ω × (IndexedSample d n) =>
      H (encodeDesignResponse a z.2)) := (hH.comp (encodeDesignResponse_measurable a)).comp measurable_snd
  have hpabs ω x : |p ω x| ≤ |bRaw| := by
    grind
  have hIntRaw : Integrable (fun z =>
      highRawSampleLikelihood a V (p z.1) (F z.1) z.2 * H (encodeDesignResponse a z.2))
      (ν.prod (highSampleReference d n)) := by
    apply Integrable.of_bound ((highRawSampleLikelihood_joint_measurable n a V hp hF).mul hM).aestronglyMeasurable
      (|bRaw| ^ n * B)
    exact Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
      exact mul_le_mul (highRawSampleLikelihood_abs_le (abs_nonneg _)
        (hpabs z.1) ha (hq z.1) z.2) (hHb _) (abs_nonneg _) (by positivity)
  have he := massPowerTilt_highSample_integral ν n hp hF haRaw hraw hq
    (fun z => H (encodeDesignResponse a z.2))
  rw [Measure.integral_compProd (by
    apply Integrable.of_bound hM.aestronglyMeasurable B
    solve_by_elim [Eventually.of_forall]), MeasureTheory.integral_prod _ hIntRaw] at he
  convert he using 1
  · apply integral_congr_ae
    exact Eventually.of_forall fun ω => by
      dsimp
      rw [highRealSampleKernel_apply,
        integral_map_of_stronglyMeasurable (encodeDesignResponse_measurable a) hH.stronglyMeasurable]
  · congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun ω => by
      apply integral_congr_ae
      exact Eventually.of_forall fun z => mul_comm _ _

end NearlyMinimax
