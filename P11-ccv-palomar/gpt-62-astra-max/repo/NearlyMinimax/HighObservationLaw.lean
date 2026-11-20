module

public import NearlyMinimax.HighPriorModel
public import NearlyMinimax.LowMixtureLaw
public import Mathlib.Probability.Kernel.Composition.WithDensity

@[expose] public section

/-! Genuine normalized high-prior observation laws. Positivity of the raw
 density makes every raw state a probability experiment; the exceptional
 mass-concentration event is not needed for probability normalization. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

section
variable {d : ℕ} {p : Covariate d → ℝ} (hp : Measurable p) {a b : ℝ} (ha : 0 < a)
    (hb : ∀ᵐ x ∂cubeVolume d, a ≤ p x ∧ p x ≤ b)
include ha hb hp

theorem highRawDensity_integrable_of_interval :
    Integrable p (cubeVolume d) := by
  let _ := cubeVolume_isProbability d
  apply (integrable_const b).mono' hp.aestronglyMeasurable
  filter_upwards [hb] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (ha.le.trans hx.1)]
  exact hx.2

theorem highRawDensityMass_mem_Icc :
    highRawDensityMass p ∈ Icc a b := by
  let _ := cubeVolume_isProbability d
  have hi := highRawDensity_integrable_of_interval hp ha hb
  constructor
  · simpa [highRawDensityMass] using
      integral_mono_ae (integrable_const a) hi (hb.mono fun x hx => hx.1)
  · simpa [highRawDensityMass] using
      integral_mono_ae hi (integrable_const b) (hb.mono fun x hx => hx.2)

theorem normalizedDensityTernaryParameter_design_probability :
    IsProbabilityMeasure ((cubeVolume d).withDensity
      (fun x => ENNReal.ofReal (highNormalizedDensity p x))) := by
  constructor
  simpa using highNormalizedDensity_normalized (highRawDensity_integrable_of_interval hp ha hb)
    (hb.mono fun x hx => ha.le.trans hx.1) (ha.trans_le (highRawDensityMass_mem_Icc hp ha hb).1)

end

variable {d n : ℕ} {α : Type*}

theorem responseSampleIndexKernel_eq_withDensity [MeasurableSpace α]
    (n : ℕ) (a V : ℝ) (F : α → ℝ) (hF : Measurable F) :
    responseSampleIndexKernel n a V hF =
      (Kernel.const (Fin n → α) Measure.count).withDensity
        (fun x y => ENNReal.ofReal (∏ i, ternaryMass a (F (x i)) V (y i))) := by
  ext x : 1
  rw [Kernel.withDensity_apply _ (by
    fun_prop)]
  simp [Kernel.const_apply, count_withDensity, Measure.sum_fintype,
    responseSampleIndexKernel_apply]

theorem fintype_probability_pi_withDensity {κ α : Type*} [Fintype κ]
    [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {f : α → ℝ≥0∞} (hf : Measurable f) (hprob : IsProbabilityMeasure (μ.withDensity f)) :
    Measure.pi (fun _ => μ.withDensity f) =
      (Measure.pi (fun _ : κ => μ)).withDensity (fun x => ∏ i, f (x i)) := by
  let _ := hprob
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator]
  · have he x :
        (Set.pi Set.univ s).indicator (fun x => ∏ i, f (x i)) x =
          ∏ i, (s i).indicator f (x i) := by
      by_cases h : ∀ i, x i ∈ s i
      · simp_all
      · obtain ⟨i, hi⟩ := not_forall.mp h
        have hz : ∏ j, (s j).indicator f (x j) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi f)
        simp_all
    simp_rw [he]
    have hG  := fun i => hf.indicator (hs i)
    rw [lintegral_prod_eq_prod_lintegral_of_indepFun _ _
      (iIndepFun_pi (fun i => (hG i).aemeasurable))
      (fun i => (hG i).comp (measurable_pi_apply i))]
    apply Finset.prod_congr rfl
    intro i _
    rw [(measurePreserving_eval (fun _ => μ) i).lintegral_comp (hG i)]
    rw [lintegral_indicator (hs i), withDensity_apply f (hs i)]
  · exact MeasurableSet.univ_pi hs

def highSampleLikelihood (a V : ℝ)
    (p F : Covariate d → ℝ) (z : IndexedSample d n) : ℝ :=
  (∏ i, p (z.1 i)) / highRawDensityMass p ^ n *
    ∏ i, ternaryMass a (F (z.1 i)) V (z.2 i)

/-- Exact iid sample density with the raw mass raised to the sample size. -/
theorem highSample_index_density (n : ℕ) {p F : Covariate d → ℝ}
    (hp : Measurable p) (hF : Measurable F) (a V : ℝ)
    (hdesign : IsProbabilityMeasure ((cubeVolume d).withDensity
      (fun x => ENNReal.ofReal (highNormalizedDensity p x))))
    (hraw : ∀ x, 0 ≤ p x) (hm : 0 < highRawDensityMass p)
    (hq0 : ∀ x y, 0 ≤ ternaryMass a (F x) V y) :
    ((Measure.pi (fun _ => (cubeVolume d).withDensity
      (fun x => ENNReal.ofReal (highNormalizedDensity p x)))).compProd
      (responseSampleIndexKernel n a V hF)) =
    ((Measure.pi (fun _ => cubeVolume d)).prod
      Measure.count).withDensity
        (fun z => ENNReal.ofReal (highSampleLikelihood a V p F z)) := by
  let _ := cubeVolume_isProbability d
  have hf : Measurable (fun x => ENNReal.ofReal (highNormalizedDensity p x)) :=
    ENNReal.measurable_ofReal.comp (hp.div_const _)
  have hq : Measurable (fun z : IndexedSample d n =>
      ENNReal.ofReal (∏ i, ternaryMass a (F (z.1 i)) V (z.2 i))) := by
    fun_prop
  let _ := Kernel.isSFiniteKernel_withDensity_of_isFiniteKernel
    (f := fun x y => ENNReal.ofReal (∏ i, ternaryMass a (F (x i)) V (y i)))
    (Kernel.const (DesignSample d n) (Measure.count : Measure (TernaryVector n)))
    (fun _ _ => ENNReal.ofReal_ne_top)
  rw [fintype_probability_pi_withDensity hf hdesign,
    responseSampleIndexKernel_eq_withDensity,
    Measure.withDensity_compProd_withDensity
      (f := fun x : DesignSample d n => ∏ i, ENNReal.ofReal (highNormalizedDensity p (x i)))
      (Finset.measurable_prod _ (fun i _ => hf.comp (measurable_pi_apply i))) hq,
    Measure.compProd_const]
  congr 1
  funext z
  have hpn i : 0 ≤ highNormalizedDensity p (z.1 i) :=
    div_nonneg (hraw _) hm.le
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => hpn i),
    ← ENNReal.ofReal_mul (Finset.prod_nonneg (fun i _ => hpn i))]
  simp [highSampleLikelihood, highNormalizedDensity, Finset.prod_div_distrib]

end NearlyMinimax
