module

public import NearlyMinimax.HighPriorModel
public import NearlyMinimax.LowMixtureLaw
public import NearlyMinimax.ProductDensity
public import NearlyMinimax.RealDensity
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

def highNormalizedDesignLaw {d : ℕ} (p : Covariate d → ℝ) : Measure (Covariate d) :=
  (cubeVolume d).withDensity (fun x => ENNReal.ofReal (highNormalizedDensity p x))

section
variable {d : ℕ} (p : Covariate d → ℝ)

section
variable (hp : Measurable p) (a b : ℝ) (ha : 0 < a)
    (hb : ∀ᵐ x ∂cubeVolume d, a ≤ p x ∧ p x ≤ b)
include hp ha hb

theorem highRawDensity_integrable_of_interval :
    Integrable p (cubeVolume d) := by
  let _ := cubeVolume_isProbability d
  exact integrable_of_ae_mem_nonneg_Icc hp ha.le hb

theorem highRawDensityMass_mem_Icc :
    highRawDensityMass p ∈ Icc a b := by
  let _ := cubeVolume_isProbability d
  exact integral_mem_Icc_of_ae_mem_Icc (highRawDensity_integrable_of_interval p hp a b ha hb) hb

theorem high_normalized_design_probability :
    IsProbabilityMeasure (highNormalizedDesignLaw p) := realDensity_probability (highRawDensity_integrable_of_interval p hp a b ha hb)
    (hb.mono fun _ hx => ha.le.trans hx.1) (ha.trans_le (highRawDensityMass_mem_Icc p hp a b ha hb).1)

end

theorem normalizedDensityTernaryParameter_sample_index_map (hdesign : IsProbabilityMeasure (highNormalizedDesignLaw p))
    (n : ℕ) (a V : ℝ) (F : Covariate d → ℝ) (hF : Measurable F) (ha : a ≠ 0)
    (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y) :
    ((Measure.pi (fun _ : Fin n => (cubeVolume d).withDensity (fun x => ENNReal.ofReal (highNormalizedDensity p x)))).compProd
      (responseSampleIndexKernel n a V F hF)).map (encodeDesignResponse a) =
      sampleLaw (normalizedDensityTernaryParameter p F a V hF ha hp) n := by
  let _ := hdesign
  exact responseSampleIndexKernel_encoded_map (highNormalizedDesignLaw p) n a V F hF ha hp

end

theorem highRawDensityMass_joint_mem_Icc {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {p : Ω → Covariate d → ℝ} (hp : Measurable (Function.uncurry p)) {a b : ℝ}
    (ha : 0 < a) (hb : ∀ ω x, a ≤ p ω x ∧ p ω x ≤ b) (ω : Ω) :
    highRawDensityMass (p ω) ∈ Icc a b :=
  highRawDensityMass_mem_Icc (p ω) hp.of_uncurry_left a b ha (.of_forall (hb ω))

section
variable {α : Type*} [MeasurableSpace α]

section
variable (n : ℕ) (a V : ℝ) (F : α → ℝ) (hF : Measurable F)
include hF

private theorem sampleResponseProduct_measurable :
    Measurable (fun z : (Fin n → α) × (Fin n → Fin 3) =>
      ENNReal.ofReal (∏ i, ternaryMass a (F (z.1 i)) V (z.2 i))) :=
  measurable_from_prod_countable_left fun y => ENNReal.measurable_ofReal.comp
    (Finset.measurable_prod _ (fun i _ =>
      ternaryMass_measurable_comp a V _ (hF.comp (measurable_pi_apply i)) (y i)))

theorem responseSampleIndexKernel_eq_withDensity :
    responseSampleIndexKernel n a V F hF =
      (Kernel.const (Fin n → α) (Measure.count : Measure (Fin n → Fin 3))).withDensity
        (fun x y => ENNReal.ofReal (∏ i, ternaryMass a (F (x i)) V (y i))) := by
  ext x : 1
  rw [Kernel.withDensity_apply _ (sampleResponseProduct_measurable n a V F hF)]
  simp only [Kernel.const_apply, count_withDensity, Measure.sum_fintype,
    responseSampleIndexKernel_apply]

end

end

/-- The unnormalized product likelihood appearing in the weak generator. -/
def highRawSampleLikelihood {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Covariate d → ℝ) (z : TernarySample d n) : ℝ :=
  ∏ i, p (z.1 i) * ternaryMass a (F (z.1 i)) V (z.2 i)

def highSampleLikelihood {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Covariate d → ℝ) (z : TernarySample d n) : ℝ :=
  highRawSampleLikelihood n a V p F z / highRawDensityMass p ^ n

/-- Exact iid sample density with the raw mass raised to the sample size. -/
theorem highSample_index_density {d : ℕ} (n : ℕ) (p F : Covariate d → ℝ)
    (hp : Measurable p) (hF : Measurable F) (a V : ℝ)
    (hdesign : IsProbabilityMeasure (highNormalizedDesignLaw p))
    (hraw : ∀ x, 0 ≤ p x) (hm : 0 < highRawDensityMass p) :
    ((Measure.pi (fun _ : Fin n => (cubeVolume d).withDensity
      (fun x => ENNReal.ofReal (highNormalizedDensity p x)))).compProd
      (responseSampleIndexKernel n a V F hF)) =
    ((Measure.pi (fun _ : Fin n => cubeVolume d)).prod
      (Measure.count : Measure (Fin n → Fin 3))).withDensity
        (fun z => ENNReal.ofReal (highSampleLikelihood n a V p F z)) := by
  let _ := cubeVolume_isProbability d
  have hf : Measurable (fun x => ENNReal.ofReal (highNormalizedDensity p x)) :=
    ENNReal.measurable_ofReal.comp (highNormalizedDensity_measurable p hp)
  let _ := Kernel.isSFiniteKernel_withDensity_of_isFiniteKernel
    (f := fun x y => ENNReal.ofReal (∏ i, ternaryMass a (F (x i)) V (y i)))
    (Kernel.const (Fin n → Covariate d) (Measure.count : Measure (Fin n → Fin 3)))
    (fun _ _ => ENNReal.ofReal_ne_top)
  rw [fintype_probability_pi_withDensity (cubeVolume d) _ hf hdesign,
    responseSampleIndexKernel_eq_withDensity,
    Measure.withDensity_compProd_withDensity
      (f := fun x : Fin n → Covariate d => ∏ i, ENNReal.ofReal (highNormalizedDensity p (x i)))
      (g := fun (x : Fin n → Covariate d) (y : Fin n → Fin 3) => ENNReal.ofReal (∏ i, ternaryMass a (F (x i)) V (y i)))
      (Finset.measurable_prod _ (fun i _ => hf.comp (measurable_pi_apply i))) (sampleResponseProduct_measurable n a V F hF),
    Measure.compProd_const]
  congr 1
  funext z
  have hpn (i : Fin n) : 0 ≤ highNormalizedDensity p (z.1 i) :=
    div_nonneg (hraw (z.1 i)) hm.le
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => hpn i),
    ← ENNReal.ofReal_mul (Finset.prod_nonneg (fun i _ => hpn i))]
  congr 1
  simp [highSampleLikelihood, highRawSampleLikelihood, highNormalizedDensity,
    Finset.prod_div_distrib, Finset.prod_mul_distrib, div_mul_eq_mul_div]

end NearlyMinimax
