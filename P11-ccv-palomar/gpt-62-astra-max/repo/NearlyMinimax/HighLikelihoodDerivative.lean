module

public import NearlyMinimax.HighMassTiltObservable
public import NearlyMinimax.HighObservableProductRule
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

section
variable {d n : ℕ} (a V v η t : ℝ) (p F : Covariate d → ℝ) (z : IndexedSample d n)

def highRawSampleVarianceDerivative : ℝ :=
  (∏ i, p (z.1 i)) * ∑ i, (∏ j ∈ Finset.univ.erase i,
    ternaryMass a (F (z.1 j)) V (z.2 j)) * ternaryVarianceDerivative a (z.2 i)

theorem highRawSampleLikelihood_hasDerivAt_variance :
    HasDerivAt (fun W => highRawSampleLikelihood a W p F z)
      (highRawSampleVarianceDerivative a V p F z) V := by
  have h := (HasDerivAt.fun_finsetProd (u := Finset.univ)
    (fun i _ => ternary_hasDerivAt_variance a (F (z.1 i)) V (z.2 i))).const_mul
      (∏ i, p (z.1 i))
  simpa only [highRawSampleLikelihood, highRawSampleVarianceDerivative,
    Finset.prod_mul_distrib, smul_eq_mul] using h

theorem highRawSampleLikelihood_hasDerivAt_path :
    HasDerivAt (fun u => highRawSampleLikelihood a (v - η ^ 2 * u) p F z)
      (-η ^ 2 * highRawSampleVarianceDerivative a (v - η ^ 2 * t) p F z) t := by
  have h := (highRawSampleLikelihood_hasDerivAt_variance a (v - η ^ 2 * t) p F z).comp t
    ((hasDerivAt_const t v).sub ((hasDerivAt_id t).const_mul (η ^ 2)))
  simpa only [Function.comp_def, Pi.sub_apply, id_eq, zero_sub, mul_one, mul_comm] using h

end

variable {d n : ℕ} {a V P : ℝ} (ha : 0 < a) (hP : 0 ≤ P) {p F : Covariate d → ℝ} (hp : ∀ x, |p x| ≤ P)

include hP hp in
theorem highRawSampleLikelihood_abs_le (ha : a ≠ 0)
    (hq : ∀ x y, 0 ≤ ternaryMass a (F x) V y)
    (z : IndexedSample d n) :
    |highRawSampleLikelihood a V p F z| ≤ P ^ n := by
  unfold highRawSampleLikelihood
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ _i, P := by
      apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
      intro i _
      rw [abs_mul, abs_of_nonneg (hq ..)]
      calc
        _ ≤ _ :=
          mul_le_mul (hp _) (ternary_mass_le_one _ V ha (hq _) _) (hq _ _) hP
        _ = P := mul_one _
    _ = _ := by simp

include ha hP hp in
theorem highRawSampleVarianceDerivative_abs_le (hq : ∀ x y, 0 ≤ ternaryMass a (F x) V y)
    (z : IndexedSample d n) :
    |highRawSampleVarianceDerivative a V p F z| ≤ P ^ n * (n / a ^ 2) := by
  have hpp : |∏ i, p (z.1 i)| ≤ P ^ n := by
    rw [Finset.abs_prod]
    simpa using Finset.prod_le_prod₀ (fun i _ => by positivity)
      (fun i (_ : i ∈ Finset.univ) => hp (z.1 i))
  have hqprod i :
      |∏ j ∈ Finset.univ.erase i, ternaryMass a (F (z.1 j)) V (z.2 j)| ≤ 1 := by
    rw [Finset.abs_prod]
    exact Finset.prod_le_one₀ (fun j _ => abs_nonneg _) (fun j _ => by
      grind [ternary_mass_le_one _ V ha.ne' (hq _) _])
  have hs : |∑ i, (∏ j ∈ Finset.univ.erase i,
      ternaryMass a (F (z.1 j)) V (z.2 j)) * ternaryVarianceDerivative a (z.2 i)| ≤
        n / a ^ 2 := by
    calc
      _ ≤ _ :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i, 1 / a ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        exact (mul_le_mul (hqprod i) (ternary_variance_derivative_abs_bound ha _)
          (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
      _ = _ := by simp [div_eq_mul_inv]
  rw [highRawSampleVarianceDerivative, abs_mul]
  bound

theorem highRawSampleVarianceDerivative_joint_measurable (n : ℕ) (a V : ℝ)
    {p F : Ω → Covariate d → ℝ} (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) :
    Measurable (fun z : Ω × (IndexedSample d n) =>
      highRawSampleVarianceDerivative a V (p z.1) (F z.1) z.2) := by
  fun_prop [highRawSampleVarianceDerivative]

end NearlyMinimax
