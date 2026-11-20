module

public import NearlyMinimax.HighMassTilt
public import NearlyMinimax.LowSmoothnessVariance


@[expose] public section

/-! Actual raw ternary likelihood derivatives for the high-prior observable product rule. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω]

def highRawSampleVarianceDerivative {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Covariate d → ℝ) (z : TernarySample d n) : ℝ :=
  (∏ i, p (z.1 i)) * ∑ i, (∏ j ∈ Finset.univ.erase i,
    ternaryMass a (F (z.1 j)) V (z.2 j)) * ternaryVarianceDerivative a (z.2 i)

section
variable {d : ℕ} (n : ℕ)

theorem highRawSampleLikelihood_hasDerivAt_variance (a V : ℝ)
    (p F : Covariate d → ℝ) (z : TernarySample d n) :
    HasDerivAt (fun W => highRawSampleLikelihood n a W p F z)
      (highRawSampleVarianceDerivative n a V p F z) V := by
  have h := (HasDerivAt.fun_finsetProd (u := (Finset.univ : Finset (Fin n)))
    (fun i _ => ternary_hasDerivAt_variance a (F (z.1 i)) V (z.2 i))).const_mul
      (∏ i, p (z.1 i))
  simpa only [highRawSampleLikelihood, highRawSampleVarianceDerivative,
    Finset.prod_mul_distrib, smul_eq_mul] using h

theorem highRawSampleLikelihood_hasDerivAt_path (a v η t : ℝ)
    (p F : Covariate d → ℝ) (z : TernarySample d n) :
    HasDerivAt (fun u => highRawSampleLikelihood n a (v - η ^ 2 * u) p F z)
      (-η ^ 2 * highRawSampleVarianceDerivative n a (v - η ^ 2 * t) p F z) t := by
  have h := (highRawSampleLikelihood_hasDerivAt_variance n a (v - η ^ 2 * t) p F z).comp t
    ((hasDerivAt_const t v).sub ((hasDerivAt_id t).const_mul (η ^ 2)))
  simpa only [Function.comp_def, Pi.sub_apply, id_eq, zero_sub, mul_one, mul_comm] using h

section
variable (a V P : ℝ)

theorem highRawSampleLikelihood_abs_le
    (p F : Covariate d → ℝ) (hp : ∀ x, |p x| ≤ P) (ha : a ≠ 0)
    (hq : ∀ x y, 0 ≤ ternaryMass a (F x) V y)
    (z : TernarySample d n) :
    |highRawSampleLikelihood n a V p F z| ≤ P ^ n := by
  unfold highRawSampleLikelihood
  simpa using abs_prod_le_pow (s := (Finset.univ : Finset (Fin n))) (B := P) (fun i _ => by
    rw [abs_mul, abs_of_nonneg (hq _ _)]
    exact (mul_le_of_le_one_right (abs_nonneg _) (ternary_mass_le_one a _ V ha (hq _) _)).trans (hp _))

theorem highRawSampleVarianceDerivative_abs_le
    (ha : 0 < a) (hP : 0 ≤ P) (p F : Covariate d → ℝ)
    (hp : ∀ x, |p x| ≤ P) (hq : ∀ x y, 0 ≤ ternaryMass a (F x) V y)
    (z : TernarySample d n) :
    |highRawSampleVarianceDerivative n a V p F z| ≤ P ^ n * ((n : ℝ) / a ^ 2) := by
  rw [highRawSampleVarianceDerivative, abs_mul]
  gcongr
  · simpa using abs_prod_le_pow (s := (Finset.univ : Finset (Fin n))) (fun (i : Fin n) _ => hp (z.1 i))
  · simpa [finiteProductFirst, div_eq_mul_inv] using
      finite_product_first_abs_bound (Finset.univ : Finset (Fin n))
        (fun i W => ternaryMass a (F (z.1 i)) W (z.2 i)) (fun i _ => ternaryVarianceDerivative a (z.2 i)) V
        (1 / a ^ 2) (fun i _ => by
          rw [abs_of_nonneg (hq (z.1 i) (z.2 i))]
          exact ternary_mass_le_one a _ V ha.ne' (hq _) _)
        (fun i _ => ternary_variance_derivative_abs_bound a ha (z.2 i))

theorem highRawSampleVarianceDerivative_params_measurable {X : Type*} [MeasurableSpace X] (a : ℝ)
    {p F : Ω → Covariate d → ℝ} (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) {ω : X → Ω} {z : X → TernarySample d n} {V : X → ℝ}
    (hω : Measurable ω) (hz : Measurable z) (hV : Measurable V) :
    Measurable (fun x => highRawSampleVarianceDerivative n a (V x) (p (ω x)) (F (ω x)) (z x)) :=
  (Finset.measurable_prod _ (fun i _ => highSample_design_measurable hp hω hz i)).mul
    (Finset.measurable_sum _ (fun i _ =>
      (Finset.measurable_prod _ (fun j _ => highSample_response_measurable a hF hω hz hV j)).mul
        ((measurable_of_countable (ternaryVarianceDerivative a)).comp ((measurable_pi_apply i).comp hz.snd))))

end

theorem highRawSampleVarianceDerivative_joint_measurable (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) :
    Measurable (fun z : Ω × TernarySample d n =>
      highRawSampleVarianceDerivative n a V (p z.1) (F z.1) z.2) :=
  highRawSampleVarianceDerivative_params_measurable n a hp hF measurable_fst measurable_snd measurable_const

end

end NearlyMinimax
