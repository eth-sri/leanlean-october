module

public import NearlyMinimax.HighObservationReal


@[expose] public section

/-! Genuine positive mass-power prior tilts and normalization cancellation. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω]

section
variable (μ : Measure Ω) (m : Ω → ℝ) (n : ℕ)

def massPowerNormalizer : ℝ :=
  ∫ ω, m ω ^ n ∂μ

def massPowerTilt : Measure Ω :=
  μ.withDensity (fun ω => ENNReal.ofReal (m ω ^ n / massPowerNormalizer μ m n))

end

section
variable (μ : Measure Ω) [IsProbabilityMeasure μ] {m : Ω → ℝ} (hm : Measurable m) (n : ℕ) {a b : ℝ}
    (ha : 0 < a) (hbound : ∀ ω, a ≤ m ω ∧ m ω ≤ b)
include ha hbound hm

theorem massPower_integrable : Integrable (fun ω => m ω ^ n) μ := by
  apply (integrable_const (b ^ n)).mono' (hm.pow_const n).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ω
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (ha.le.trans (hbound ω).1) n)]
  exact pow_le_pow_left₀ (ha.le.trans (hbound ω).1) (hbound ω).2 n

theorem massPowerNormalizer_mem_Icc :
    massPowerNormalizer μ m n ∈ Icc (a ^ n) (b ^ n) := by
  have hi := massPower_integrable μ hm n ha hbound
  constructor
  · simpa [massPowerNormalizer] using integral_mono_ae (integrable_const (a ^ n)) hi
      (Filter.Eventually.of_forall (fun ω => pow_le_pow_left₀ ha.le (hbound ω).1 n))
  · simpa [massPowerNormalizer] using integral_mono_ae hi (integrable_const (b ^ n))
      (Filter.Eventually.of_forall (fun ω =>
        pow_le_pow_left₀ (ha.le.trans (hbound ω).1) (hbound ω).2 n))

theorem massPowerNormalizer_pos : 0 < massPowerNormalizer μ m n :=
  (pow_pos ha n).trans_le (massPowerNormalizer_mem_Icc μ hm n ha hbound).1

theorem massPowerTilt_isProbability : IsProbabilityMeasure (massPowerTilt μ m n) := by
  have hG := massPowerNormalizer_pos μ hm n ha hbound
  constructor
  rw [massPowerTilt, withDensity_apply _ MeasurableSet.univ]
  simp
  rw [← ofReal_integral_eq_lintegral_ofReal ((massPower_integrable μ hm n ha hbound).div_const _)
    (Filter.Eventually.of_forall (fun ω =>
      div_nonneg (pow_nonneg (ha.le.trans (hbound ω).1) n) hG.le)), integral_div]
  change ENNReal.ofReal (massPowerNormalizer μ m n / massPowerNormalizer μ m n) = 1
  rw [div_self hG.ne', ENNReal.ofReal_one]

end

section
variable {μ ν : Measure Ω} {m : Ω → ℝ} {Α : Type*} (hm : Measurable m) (n : ℕ) (hlaw : μ.map m = ν.map m)

include hm hlaw in
/-- Equality of actual mass laws makes the power normalizer time independent. -/
theorem massPowerNormalizer_eq_of_massLaw :
    massPowerNormalizer μ m n = massPowerNormalizer ν m n := by
  have hμ := integral_map_of_stronglyMeasurable (μ := μ) hm
    ((measurable_id.pow_const n).stronglyMeasurable)
  rw [hlaw] at hμ
  exact hμ.symm.trans (integral_map_of_stronglyMeasurable (μ := ν) hm ((measurable_id.pow_const n).stronglyMeasurable))

/-- Pushing a pullback density forward gives the density of the pushed-forward law. -/
theorem map_withDensity_pullback [MeasurableSpace Α]
    (μ : Measure Ω) {m : Ω → Α} (hm : Measurable m)
    {f : Α → ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity (fun ω => f (m ω))).map m = (μ.map m).withDensity f := by
  apply Measure.ext_of_lintegral
  intro G hG
  have hfm : Measurable (fun ω => f (m ω)) := hf.comp hm
  have hGm : Measurable (fun ω => G (m ω)) := hG.comp hm
  rw [lintegral_map hG hm,
    lintegral_withDensity_eq_lintegral_mul _ hfm hGm,
    lintegral_withDensity_eq_lintegral_mul _ hf hG,
    lintegral_map (hf.mul hG) hm]
  rfl

include hm hlaw in
/-- The tilted mass law, hence its exceptional mass probabilities, depends
only on the original mass law. -/
theorem massPowerTilt_massLaw_eq :
    (massPowerTilt μ m n).map m = (massPowerTilt ν m n).map m := by
  unfold massPowerTilt
  rw [(massPowerNormalizer_eq_of_massLaw hm n hlaw)]
  have hf : Measurable (fun x => ENNReal.ofReal (x ^ n / massPowerNormalizer ν m n)) :=
    by fun_prop
  rw [map_withDensity_pullback μ hm hf, map_withDensity_pullback ν hm hf, hlaw]

end

variable {d : ℕ} (n : ℕ) (a V : ℝ)

/-- The unnormalized product likelihood appearing in the weak generator. -/
def highRawSampleLikelihood {n : ℕ} (a V : ℝ)
    (p F : Covariate d → ℝ) (z : IndexedSample d n) : ℝ :=
  ∏ i, p (z.1 i) * ternaryMass a (F (z.1 i)) V (z.2 i)

theorem highRawSampleLikelihood_joint_measurable
    {p F : Ω → Covariate d → ℝ} (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) :
    Measurable (fun z : Ω × (IndexedSample d n) =>
      highRawSampleLikelihood a V (p z.1) (F z.1) z.2) := by
  fun_prop [highRawSampleLikelihood]

theorem highSampleLikelihood_mass_cancellation
    {p : Covariate d → ℝ} (F : Covariate d → ℝ) (hm : highRawDensityMass p ≠ 0)
    (z : IndexedSample d n) :
    highRawDensityMass p ^ n * highSampleLikelihood a V p F z =
      highRawSampleLikelihood a V p F z := by
  simp only [highSampleLikelihood, highRawSampleLikelihood, Finset.prod_mul_distrib]
  field_simp

instance highSampleIndexKernel_isSFinite
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) : IsSFiniteKernel (highSampleIndexKernel n a V hp hF) := by
  change IsSFiniteKernel ((Kernel.const Ω (highSampleReference d n)).withDensity
    (fun ω z => ENNReal.ofReal (highSampleLikelihood a V (p ω) (F ω) z)))
  exact Kernel.isSFiniteKernel_withDensity_of_isFiniteKernel _ (fun _ _ => ENNReal.ofReal_ne_top)

/-- The actual tilted-prior/sample measure has the raw product likelihood
 divided only by the prior normalizer. -/
theorem massPowerTilt_highSample_compProd (ν : Measure Ω) [IsProbabilityMeasure ν]
    (n : ℕ) (a V : ℝ) {p F : Ω → Covariate d → ℝ}
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    {aRaw bRaw : ℝ} (haRaw : 0 < aRaw)
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw) :
    (massPowerTilt ν (fun ω => highRawDensityMass (p ω)) n).compProd
      (highSampleIndexKernel n a V hp hF) =
      (ν.prod (highSampleReference d n)).withDensity (fun z =>
        ENNReal.ofReal (highRawSampleLikelihood a V (p z.1) (F z.1) z.2 /
          massPowerNormalizer ν (fun ω => highRawDensityMass (p ω)) n)) := by
  let m  := fun ω => highRawDensityMass (p ω)
  have hbound ω  :=
    highRawDensityMass_mem_Icc hp.of_uncurry_left haRaw
      (Filter.Eventually.of_forall (hraw ω))
  have hG := massPowerNormalizer_pos ν (highRawDensityMass_joint_measurable hp) n haRaw hbound
  have hL  :=
    ENNReal.measurable_ofReal.comp (highSampleLikelihood_joint_measurable n a V hp hF)
  let _ := Kernel.isSFiniteKernel_withDensity_of_isFiniteKernel
    (f := fun ω z => ENNReal.ofReal (highSampleLikelihood a V (p ω) (F ω) z))
    (Kernel.const Ω (highSampleReference d n)) (fun _ _ => ENNReal.ofReal_ne_top)
  change (ν.withDensity (fun ω => ENNReal.ofReal (m ω ^ n / massPowerNormalizer ν m n))).compProd
    ((Kernel.const Ω (highSampleReference d n)).withDensity
      (fun ω z => ENNReal.ofReal (highSampleLikelihood a V (p ω) (F ω) z))) = _
  rw [Measure.withDensity_compProd_withDensity
    (g := fun ω z => ENNReal.ofReal (highSampleLikelihood a V (p ω) (F ω) z)) (by fun_prop) hL,
    Measure.compProd_const]
  congr 1
  funext z
  rw [← ENNReal.ofReal_mul (div_nonneg (pow_nonneg (haRaw.le.trans (hbound z.1).1) n) hG.le)]
  congr 1
  calc
    _ =
        (m z.1 ^ n * highSampleLikelihood a V (p z.1) (F z.1) z.2) / massPowerNormalizer ν m n := by ring
    _ = _ := by rw [highSampleLikelihood_mass_cancellation n a V (F z.1)
      (haRaw.trans_le (hbound z.1).1).ne']

end NearlyMinimax
