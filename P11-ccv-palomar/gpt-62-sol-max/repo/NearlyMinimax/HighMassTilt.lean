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

def massPowerNormalizer (μ : Measure Ω) (m : Ω → ℝ) (n : ℕ) : ℝ :=
  ∫ ω, m ω ^ n ∂μ

def massPowerTilt (μ : Measure Ω) (m : Ω → ℝ) (n : ℕ) : Measure Ω :=
  μ.withDensity (fun ω => ENNReal.ofReal (m ω ^ n / massPowerNormalizer μ m n))

theorem massPower_mem_Icc {m : Ω → ℝ} {a b : ℝ} (ha : 0 ≤ a)
    (hbound : ∀ ω, m ω ∈ Icc a b) (n : ℕ) (ω : Ω) :
    m ω ^ n ∈ Icc (a ^ n) (b ^ n) :=
  ⟨pow_le_pow_left₀ ha (hbound ω).1 n, pow_le_pow_left₀ (ha.trans (hbound ω).1) (hbound ω).2 n⟩

section
variable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : Ω → ℝ) (hm : Measurable m) (n : ℕ) (a b : ℝ) (ha : 0 < a)
    (hbound : ∀ ω, a ≤ m ω ∧ m ω ≤ b)
include hm ha hbound

theorem massPower_integrable : Integrable (fun ω => m ω ^ n) μ :=
  integrable_of_ae_mem_nonneg_Icc (hm.pow_const n) (pow_nonneg ha.le n)
    (.of_forall (massPower_mem_Icc ha.le hbound n))

theorem massPowerNormalizer_mem_Icc :
    massPowerNormalizer μ m n ∈ Icc (a ^ n) (b ^ n) :=
  integral_mem_Icc_of_ae_mem_Icc (massPower_integrable μ m hm n a b ha hbound)
    (.of_forall (massPower_mem_Icc ha.le hbound n))

theorem massPowerNormalizer_pos : 0 < massPowerNormalizer μ m n :=
  (pow_pos ha n).trans_le (massPowerNormalizer_mem_Icc μ m hm n a b ha hbound).1

end

/-- The real-response data law after tilting the raw prior by its sample mass. -/
abbrev highDataLaw {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (ν : Measure Ω) (n : ℕ) (a V : ℝ) (p F : Ω → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) :=
  highRealSampleKernel n a V p F hp hF ∘ₘ massPowerTilt ν (fun ω => highRawDensityMass (p ω)) n

section
variable {d : ℕ}

theorem highDataLaw_eq_map (ν : Measure Ω) (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) :
    highDataLaw ν n a V p F hp hF =
      (highSampleIndexKernel n a V p F hp hF ∘ₘ
        massPowerTilt ν (fun ω => highRawDensityMass (p ω)) n).map (encodeDesignResponse a) := by
  rw [highDataLaw, highRealSampleKernel, Measure.map_comp _ _ (encodeDesignResponse_measurable a)]

theorem highRawDensity_abs_bound {p : Ω → Covariate d → ℝ} {a b : ℝ} (ha : 0 ≤ a)
    (hraw : ∀ ω x, a ≤ p ω x ∧ p ω x ≤ b) (ω : Ω) (x : Covariate d) : |p ω x| ≤ |b| := by
  grind

end

theorem massPowerTilt_isProbability (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : Ω → ℝ) (hm : Measurable m) (n : ℕ) (a b : ℝ) (ha : 0 < a)
    (hbound : ∀ ω, a ≤ m ω ∧ m ω ≤ b) : IsProbabilityMeasure (massPowerTilt μ m n) :=
  realDensity_probability (massPower_integrable μ m hm n a b ha hbound)
    (.of_forall fun ω => pow_nonneg (ha.le.trans (hbound ω).1) n)
    (massPowerNormalizer_pos μ m hm n a b ha hbound)

/-- Equality of actual mass laws makes the power normalizer time independent. -/
theorem highMassPowerTilt_isProbability {d : ℕ} (ν : Measure Ω) [IsProbabilityMeasure ν]
    (n : ℕ) (p : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    {aRaw bRaw : ℝ} (haRaw : 0 < aRaw) (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw) :
    IsProbabilityMeasure (massPowerTilt ν (fun ω => highRawDensityMass (p ω)) n) :=
  massPowerTilt_isProbability ν _ (highRawDensityMass_joint_measurable p hp) n aRaw bRaw haRaw
    (highRawDensityMass_joint_mem_Icc hp haRaw hraw)

theorem massPowerNormalizer_eq_of_massLaw (μ ν : Measure Ω) (m : Ω → ℝ)
    (hm : Measurable m) (n : ℕ) (hlaw : μ.map m = ν.map m) :
    massPowerNormalizer μ m n = massPowerNormalizer ν m n := by
  have hμ := integral_map_of_stronglyMeasurable (μ := μ) hm
    ((measurable_id.pow_const n : Measurable (fun x : ℝ => x ^ n)).stronglyMeasurable)
  have hν := integral_map_of_stronglyMeasurable (μ := ν) hm
    ((measurable_id.pow_const n : Measurable (fun x : ℝ => x ^ n)).stronglyMeasurable)
  aesop

/-- Pushing a pullback density forward gives the density of the pushed-forward law. -/
theorem map_withDensity_pullback {Α : Type*} [MeasurableSpace Α]
    (μ : Measure Ω) (m : Ω → Α) (hm : Measurable m)
    (f : Α → ℝ≥0∞) (hf : Measurable f) :
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

/-- The tilted mass law, hence its exceptional mass probabilities, depends
only on the original mass law. -/
theorem massPowerTilt_massLaw_eq (μ ν : Measure Ω) (m : Ω → ℝ)
    (hm : Measurable m) (n : ℕ) (hlaw : μ.map m = ν.map m) :
    (massPowerTilt μ m n).map m = (massPowerTilt ν m n).map m := by
  have hG := massPowerNormalizer_eq_of_massLaw μ ν m hm n hlaw
  unfold massPowerTilt
  rw [hG]
  have hf : Measurable (fun x : ℝ => ENNReal.ofReal (x ^ n / massPowerNormalizer ν m n)) :=
    ENNReal.measurable_ofReal.comp ((measurable_id.pow_const n).div_const _)
  rw [map_withDensity_pullback μ m hm _ hf, map_withDensity_pullback ν m hm _ hf, hlaw]

section
variable {d : ℕ} (n : ℕ) (a V : ℝ)

theorem highSampleLikelihood_mass_cancellation
    (p F : Covariate d → ℝ) (hm : highRawDensityMass p ≠ 0)
    (z : TernarySample d n) :
    highRawDensityMass p ^ n * highSampleLikelihood n a V p F z =
      highRawSampleLikelihood n a V p F z := by
  unfold highSampleLikelihood
  field_simp

end

instance highSampleIndexKernel_isSFinite {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) : IsSFiniteKernel (highSampleIndexKernel n a V p F hp hF) := by
  apply Kernel.isSFiniteKernel_withDensity_of_isFiniteKernel <;> simp_all

/-- The actual tilted-prior/sample measure has the raw product likelihood
 divided only by the prior normalizer. -/
theorem massPowerTilt_highSample_compProd {d : ℕ} (ν : Measure Ω) [IsProbabilityMeasure ν]
    (n : ℕ) (a V : ℝ) (p F : Ω → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (aRaw bRaw : ℝ) (haRaw : 0 < aRaw)
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw) :
    (massPowerTilt ν (fun ω => highRawDensityMass (p ω)) n).compProd
      (highSampleIndexKernel n a V p F hp hF) =
      (ν.prod (highSampleReference d n)).withDensity (fun z =>
        ENNReal.ofReal (highRawSampleLikelihood n a V (p z.1) (F z.1) z.2 /
          massPowerNormalizer ν (fun ω => highRawDensityMass (p ω)) n)) := by
  let m : Ω → ℝ := fun ω => highRawDensityMass (p ω)
  have hm : Measurable m := highRawDensityMass_joint_measurable p hp
  have hbound (ω : Ω) : aRaw ≤ m ω ∧ m ω ≤ bRaw :=
    highRawDensityMass_joint_mem_Icc hp haRaw hraw ω
  have hG := massPowerNormalizer_pos ν m hm n aRaw bRaw haRaw hbound
  have hd : Measurable (fun ω => ENNReal.ofReal (m ω ^ n / massPowerNormalizer ν m n)) :=
    ENNReal.measurable_ofReal.comp ((hm.pow_const n).div_const _)
  have hL :=
    ENNReal.measurable_ofReal.comp (highSampleLikelihood_joint_measurable n a V p F hp hF)
  letI := Kernel.isSFiniteKernel_withDensity_of_isFiniteKernel
    (f := fun ω z => ENNReal.ofReal (highSampleLikelihood n a V (p ω) (F ω) z))
    (Kernel.const Ω (highSampleReference d n))
    (fun _ _ => ENNReal.ofReal_ne_top)
  change (ν.withDensity (fun ω => ENNReal.ofReal (m ω ^ n / massPowerNormalizer ν m n))).compProd
    ((Kernel.const Ω (highSampleReference d n)).withDensity
      (fun ω z => ENNReal.ofReal (highSampleLikelihood n a V (p ω) (F ω) z))) = _
  rw [Measure.withDensity_compProd_withDensity
    (κ := Kernel.const Ω (highSampleReference d n))
    (f := fun ω => ENNReal.ofReal (m ω ^ n / massPowerNormalizer ν m n))
    (g := fun ω z => ENNReal.ofReal (highSampleLikelihood n a V (p ω) (F ω) z)) hd hL,
    Measure.compProd_const]
  congr 1
  funext z
  rw [← ENNReal.ofReal_mul (div_nonneg (pow_nonneg (haRaw.le.trans (hbound z.1).1) n) hG.le)]
  congr 1
  rw [div_mul_eq_mul_div, highSampleLikelihood_mass_cancellation _ _ _ _ _
    (haRaw.trans_le (hbound z.1).1).ne']

end NearlyMinimax
