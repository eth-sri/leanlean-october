module

public import NearlyMinimax.ExponentialSpatialKernels
public import Mathlib.Probability.Independence.Integration


@[expose] public section

/-! Actual independent spatial-coordinate projections and pair integrations. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

section
variable (d : ℕ) {I J E : Type*}

/-- Actual projection onto any distinct finite spatial coordinates preserves the true independent law. -/
theorem spatialPi_projection_preserving [Fintype I] [Fintype J]
    [MeasurableSpace E] (π : Measure E) [IsProbabilityMeasure π] (e : I ↪ J) :
    MeasurePreserving (fun U => fun i => U (e i))
      (Measure.pi (fun _ => π)) (Measure.pi (fun _ => π)) := by
  have hc : iIndepFun (fun j U => U j) (Measure.pi (fun _ => π)) :=
    iIndepFun_pi (X := fun _ : J => id) (fun _ => aemeasurable_id)
  refine ⟨(by fun_prop), ?_⟩
  have he := (iIndepFun_iff_map_fun_eq_pi_map (fun i => (measurable_pi_apply (e i)).aemeasurable)).mp (iIndepFun.precomp e.injective hc)
  simpa only [(measurePreserving_eval (fun _ => π) _).map_eq] using he

/-- Scaling each genuine finite coordinate measure scales its product by the cardinal power. -/
theorem spatialPi_const_smul [Fintype J] [MeasurableSpace E]
    (π : Measure E) [SigmaFinite π] (c : ℝ≥0∞) [SigmaFinite (c • π)] :
    Measure.pi (fun _ => c • π) = c^(Fintype.card J) • Measure.pi (fun _ : J => π) := by
  classical
  apply Measure.pi_eq
  intro S hS
  rw [Measure.smul_apply, smul_eq_mul, Measure.pi_pi]
  simp [Measure.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

/-- The actual uniform probability law on the source local cube. -/
def spatialPatchProbability : Measure (Covariate d) :=
  ((2 : ℝ≥0∞)^d)⁻¹ • volume.restrict (spatialPatchBox d)

instance spatialPatchProbability_isProbability : IsProbabilityMeasure (spatialPatchProbability d) := by
  constructor
  rw [spatialPatchProbability, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ, spatialPatchBox_volume]
  exact ENNReal.inv_mul_cancel (by positivity) (by finiteness)

theorem spatialPatchProbability_le_volume : spatialPatchProbability d ≤ volume := fun S => (mul_le_of_le_one_left (show 0 ≤ (volume.restrict (spatialPatchBox d)) S from zero_le) (ENNReal.inv_le_one.mpr (one_le_pow₀ (by norm_num)))).trans (Measure.restrict_le_self S)

end

section
variable {J E : Type*} [Fintype J] [MeasurableSpace E] (π : Measure E) [IsProbabilityMeasure π] {i j : J}
    (hij : i ≠ j)
include hij

/-- Actual distinct-coordinate pair evaluation preserves the true independent product law. -/
theorem spatialPi_pair_preserving :
    MeasurePreserving (fun U => (U i, U j))
      (Measure.pi (fun _ => π)) (π.prod π) := by
  classical
  convert (measurePreserving_finTwoArrow π).comp (spatialPi_projection_preserving π (⟨![i,j], by simpa⟩)) using 1
  rfl

/-- Genuine integration through an actual pair projection. -/
theorem spatialPi_pair_integral
    {F : E × E → ℝ} (hF : Measurable F) :
    (∫ U, F (U i, U j) ∂Measure.pi (fun _ => π)) = ∫ z, F z ∂π.prod π := by
  have hp := spatialPi_pair_preserving π hij
  exact (integral_map hp.measurable.aemeasurable hF.aestronglyMeasurable).symm.trans
    (congrArg (fun μ => ∫ z, F z ∂μ) hp.map_eq)

end

/-- A true probability spatial law dominated by volume has the dimension-scaled pair exponential integral. -/
theorem spatial_probability_pair_exponential_integral_le {d : ℕ} (hd : 0 < d)
    {π : Measure (Covariate d)} [IsProbabilityMeasure π] (hπ : π ≤ volume)
    {T : ℝ} (hT : 0 < T) :
    (∫ xy, Real.exp (-(T * exactEuclideanDistance xy.1 xy.2)) ∂π.prod π) ≤
      spatialExponentialConstant d / T^d := by
  have hm  :=
    (exactEuclideanDistance_continuous (d := d) |>.const_mul T |>.neg |>.rexp).measurable
  have hi : Integrable (fun xy =>
      Real.exp (-(T * exactEuclideanDistance xy.1 xy.2))) (π.prod π) :=
    Integrable.of_bound hm.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun xy => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hT.le (exactEuclideanDistance_nonneg _ _))))
  rw [integral_prod _ hi]
  have hb x  :=
    (integral_mono_measure hπ (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)
      (exactEuclideanDistance_exponential_integrable hd hT x)).trans_eq
        (exactEuclideanDistance_exponential_integral hd hT x)
  simpa using integral_mono hi.integral_prod_left (integrable_const _) hb

variable {J E : Type*} [Fintype J]

/-- Genuine factorization of functions of two disjoint iid coordinate pairs. -/
theorem spatialPi_two_pair_functions_factor [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (q : Fin 4 ↪ J)
    {F : E × E → ℝ} (hF : Measurable F) :
    (∫ U, F (U (q 0), U (q 1)) * F (U (q 2), U (q 3))
      ∂Measure.pi (fun _ => π)) = (∫ xy, F xy ∂π.prod π)^2 := by
  have hc : iIndepFun (fun j U => U j) (Measure.pi (fun _ => π)) :=
    iIndepFun_pi (X := fun _ : J => id) (fun _ => aemeasurable_id)
  have hne i j (h : i ≠ j)  := fun he => h (q.injective he)
  have hind0 := hc.indepFun_prodMk_prodMk (fun j => measurable_pi_apply j)
    (q 0) (q 1) (q 2) (q 3)
    (hne 0 2 (by decide)) (hne 0 3 (by decide))
    (hne 1 2 (by decide)) (hne 1 3 (by decide))
  have hind := hind0.comp hF hF
  have hfm : Measurable (fun U : J → E => F (U (q 0), U (q 1))) :=
    by fun_prop
  have hgm : Measurable (fun U : J → E => F (U (q 2), U (q 3))) :=
    by fun_prop
  have he := hind.integral_mul_eq_mul_integral hfm.aestronglyMeasurable hgm.aestronglyMeasurable
  change _ = _ at he
  simp at he
  rw [spatialPi_pair_integral π (hne 0 1 (by decide)) hF,
    spatialPi_pair_integral π (hne 2 3 (by decide)) hF] at he
  simpa only [pow_two] using he

/-- Exact independence of the two actual disjoint spatial exponential pair kernels. -/
theorem spatialPi_two_pairs_integral_factor
    {d : ℕ} (π : Measure (Covariate d)) [IsProbabilityMeasure π]
    (q : Fin 4 ↪ J) (T : ℝ) :
    (∫ U,
      Real.exp (-(T * (exactEuclideanDistance (U (q 0)) (U (q 1)) +
        exactEuclideanDistance (U (q 2)) (U (q 3))))) ∂Measure.pi (fun _ => π)) =
      (∫ xy, Real.exp (-(T * exactEuclideanDistance xy.1 xy.2)) ∂π.prod π)^2 := by
  have hpair : Measurable (fun xy : Covariate d × Covariate d => Real.exp (-(T*exactEuclideanDistance xy.1 xy.2))) :=
    (exactEuclideanDistance_continuous |>.const_mul T |>.neg |>.rexp).measurable
  have he := spatialPi_two_pair_functions_factor π q hpair
  simp_rw [← Real.exp_add] at he
  simp_rw [show ∀ a b, -(T*a) + -(T*b) = -(T*(a+b)) by intros; ring] at he
  exact he

end NearlyMinimax
