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

theorem highRawDensity_integrable_of_interval  (p )
    (hp : Measurable p) (a b : ℝ) (ha : 0 < a)
    (hb : ∀ᵐ x ∂cubeVolume d, a ≤ p x ∧ p x ≤ b) :
    Integrable p (cubeVolume d) := by
  let _ := cubeVolume_isProbability d
  apply (integrable_const b).mono' hp.aestronglyMeasurable
  filter_upwards [hb] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (ha.le.trans hx.1)]
  exact hx.2

theorem highRawDensityMass_mem_Icc  (p )
    (hp : Measurable p) (a b : ℝ) (ha : 0 < a)
    (hb : ∀ᵐ x ∂cubeVolume d, a ≤ p x ∧ p x ≤ b) :
    highRawDensityMass p ∈ Icc a b := by
  let _ := cubeVolume_isProbability d
  have hi := highRawDensity_integrable_of_interval p hp a b ha hb
  constructor
  · simpa [highRawDensityMass] using
      integral_mono_ae (integrable_const a) hi (hb.mono fun x hx => hx.1)
  · simpa [highRawDensityMass] using
      integral_mono_ae hi (integrable_const b) (hb.mono fun x hx => hx.2)

theorem normalizedDensityTernaryParameter_design_probability 
    (p ) (hp : Measurable p) (a b : ℝ) (ha : 0 < a)
    (hb : ∀ᵐ x ∂cubeVolume d, a ≤ p x ∧ p x ≤ b) :
    IsProbabilityMeasure ((cubeVolume d).withDensity
      (fun x => ENNReal.ofReal (highNormalizedDensity p x))) := by
  let _ := cubeVolume_isProbability d
  constructor
  rw [withDensity_apply _ MeasurableSet.univ]
  simpa using highNormalizedDensity_normalized p (highRawDensity_integrable_of_interval p hp a b ha hb)
    (hb.mono fun x hx => ha.le.trans hx.1) (ha.trans_le (highRawDensityMass_mem_Icc p hp a b ha hb).1)

theorem responseSampleIndexKernel_eq_withDensity  [MeasurableSpace α]
    (n a V F) (hF : Measurable F) :
    responseSampleIndexKernel n a V F hF =
      (Kernel.const (Fin n → α) (Measure.count : Measure (Fin n → Fin 3))).withDensity
        (fun x y => ENNReal.ofReal (∏ i, ternaryMass a (F (x i)) V (y i))) := by
  have hq : Measurable (fun z : (Fin n → α) × (Fin n → Fin 3) =>
      ENNReal.ofReal (∏ i, ternaryMass a (F (z.1 i)) V (z.2 i))) := by
    apply measurable_from_prod_countable_left
    intro y
    apply ENNReal.measurable_ofReal.comp
    exact Finset.measurable_prod _ (fun i _ =>
      ternaryMass_measurable_comp a V (fun x : Fin n → α => F (x i))
        (hF.comp (measurable_pi_apply i)) (y i))
  ext x : 1
  rw [Kernel.withDensity_apply _ hq]
  simp only [Kernel.const_apply, count_withDensity, Measure.sum_fintype,
    responseSampleIndexKernel_apply]

/-- Density tensorization for a finite iid product, proved on measurable boxes. -/
theorem probability_pi_withDensity  [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f ) (hf : Measurable f)
    (hprob : IsProbabilityMeasure (μ.withDensity f)) (n ) :
    Measure.pi (fun _ => μ.withDensity f) =
      (Measure.pi (fun _ : Fin n => μ)).withDensity (fun x => ∏ i, f (x i)) := by
  let _ := hprob
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator]
  · have he (x : Fin n → α) :
        (Set.pi Set.univ s).indicator (fun x => ∏ i, f (x i)) x =
          ∏ i, (s i).indicator f (x i) := by
      by_cases h : ∀ i, x i ∈ s i
      · simp [Set.indicator_of_mem, Set.mem_pi, h]
      · obtain ⟨i, hi⟩ := not_forall.mp h
        rw [Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi f)]
        apply Set.indicator_of_notMem
        simp only [Set.mem_pi, Set.mem_univ, forall_true_left]
        exact not_forall.mpr ⟨i, hi⟩
    simp_rw [he]
    have hG  := fun i => hf.indicator (hs i)
    change (∫⁻ x, ∏ i, (fun i => (s i).indicator f) i (x i) ∂Measure.pi (fun _ => μ)) = _
    rw [lintegral_prod_eq_prod_lintegral_of_indepFun _ _
      (iIndepFun_pi (fun i => (hG i).aemeasurable))
      (fun i => (hG i).comp (measurable_pi_apply i))]
    apply Finset.prod_congr rfl
    intro i _
    rw [(measurePreserving_eval (fun _ => μ) i).lintegral_comp (hG i), lintegral_indicator (hs i), withDensity_apply f (hs i)]
  · exact MeasurableSet.univ_pi hs

def highSampleLikelihood  (n ) (a V : ℝ)
    (p F : Covariate d → ℝ) (z : (Fin n → Covariate d) × (Fin n → Fin 3)) : ℝ :=
  (∏ i, p (z.1 i)) / highRawDensityMass p ^ n *
    ∏ i, ternaryMass a (F (z.1 i)) V (z.2 i)

/-- Exact iid sample density with the raw mass raised to the sample size. -/
theorem highSample_index_density  (n p F)
    (hp : Measurable p) (hF : Measurable F) (a V )
    (hdesign : IsProbabilityMeasure ((cubeVolume d).withDensity
      (fun x => ENNReal.ofReal (highNormalizedDensity p x))))
    (hraw : ∀ x, 0 ≤ p x) (hm : 0 < highRawDensityMass p)
    (hq0 : ∀ x y, 0 ≤ ternaryMass a (F x) V y) :
    ((Measure.pi (fun _ => (cubeVolume d).withDensity
      (fun x => ENNReal.ofReal (highNormalizedDensity p x)))).compProd
      (responseSampleIndexKernel n a V F hF)) =
    ((Measure.pi (fun _ : Fin n => cubeVolume d)).prod
      (Measure.count : Measure (Fin n → Fin 3))).withDensity
        (fun z => ENNReal.ofReal (highSampleLikelihood n a V p F z)) := by
  let _ := cubeVolume_isProbability d
  have hf : Measurable (fun x => ENNReal.ofReal (highNormalizedDensity p x)) :=
    ENNReal.measurable_ofReal.comp (highNormalizedDensity_measurable p hp)
  have hq : Measurable (fun z : (Fin n → Covariate d) × (Fin n → Fin 3) =>
      ENNReal.ofReal (∏ i, ternaryMass a (F (z.1 i)) V (z.2 i))) := by
    apply measurable_from_prod_countable_left
    intro y
    apply ENNReal.measurable_ofReal.comp
    exact Finset.measurable_prod _ (fun i _ =>
      ternaryMass_measurable_comp a V (fun x : Fin n → Covariate d => F (x i))
        (hF.comp (measurable_pi_apply i)) (y i))
  let _ := Kernel.isSFiniteKernel_withDensity_of_isFiniteKernel
    (f := fun x y => ENNReal.ofReal (∏ i, ternaryMass a (F (x i)) V (y i)))
    (Kernel.const (Fin n → Covariate d) (Measure.count : Measure (Fin n → Fin 3)))
    (fun _ _ => ENNReal.ofReal_ne_top)
  rw [probability_pi_withDensity (cubeVolume d) _ hf hdesign n,
    responseSampleIndexKernel_eq_withDensity,
    Measure.withDensity_compProd_withDensity
      (f := fun x : Fin n → Covariate d => ∏ i, ENNReal.ofReal (highNormalizedDensity p (x i)))
      (g := fun (x : Fin n → Covariate d) (y : Fin n → Fin 3) => ENNReal.ofReal (∏ i, ternaryMass a (F (x i)) V (y i)))
      (Finset.measurable_prod _ (fun i _ => hf.comp (measurable_pi_apply i))) hq,
    Measure.compProd_const]
  congr 1
  funext z
  have hpn (i : Fin n) : 0 ≤ highNormalizedDensity p (z.1 i) :=
    div_nonneg (hraw (z.1 i)) hm.le
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => hpn i),
    ← ENNReal.ofReal_mul (Finset.prod_nonneg (fun i _ => hpn i))]
  congr 1
  simp [highSampleLikelihood, highNormalizedDensity, Finset.prod_div_distrib]

end NearlyMinimax
