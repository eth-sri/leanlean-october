module

public import NearlyMinimax.Projection


@[expose] public section

open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators

set_option maxHeartbeats 1000000

namespace NearlyMinimax

section
variable {ι Ω : Type*}

section
variable [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ε : ι → Ω → ℝ) (hind : iIndepFun ε μ)
    (hmeas : ∀ i, AEStronglyMeasurable (ε i) μ)
include hind hmeas

/-- Independence factors arbitrary finite lists of coordinate errors,
including repeated indices grouped into their multiplicities. -/
theorem independent_error_list_moment (l : List ι) :
    (∫ ω, (l.map (fun i => ε i ω)).prod ∂μ) =
      ∏ i ∈ l.toFinset, ∫ ω, ε i ω ^ l.count i ∂μ := by
  simp_rw [Finset.prod_list_map_count, ← Finset.prod_coe_sort l.toFinset]
  exact ((hind.comp (fun i x => x ^ l.count i) (fun _ => measurable_id.pow_const _)).precomp
    Subtype.val_injective).integral_fun_prod_eq_prod_integral (fun i : ↥l.toFinset => (hmeas i).pow _)

/-- The four-coordinate moment rule behind the variance of a quadratic
form, derived from actual independence and centered errors. -/
theorem independent_error_fourth_product
    (hmean : ∀ i, (∫ ω, ε i ω ∂μ) = 0) (V : ℝ)
    (hsecond : ∀ i, (∫ ω, ε i ω ^ 2 ∂μ) = V) (i j k l : ι) :
    (∫ ω, ε i ω * ε j ω * ε k ω * ε l ω ∂μ) =
      if i = j then
        if k = l then (if i = k then (∫ ω, ε i ω ^ 4 ∂μ) else V ^ 2) else 0
      else if i = k ∧ j = l then V ^ 2
      else if i = l ∧ j = k then V ^ 2 else 0 := by
  rw [show (∫ ω, ε i ω * ε j ω * ε k ω * ε l ω ∂μ) =
      ∫ ω, ([i, j, k, l].map (fun a => ε a ω)).prod ∂μ by simp; congr 1; ext; ring,
    independent_error_list_moment μ ε hind hmeas]
  by_cases hij : i = j <;> by_cases hik : i = k <;> by_cases hil : i = l <;>
    by_cases hjk : j = k <;> by_cases hjl : j = l <;> by_cases hkl : k = l <;>
    subst_vars <;> simp_all [List.toFinset_cons, List.toFinset_nil, List.count_cons, List.count_nil,
      Finset.prod_insert, Finset.prod_singleton, pow_one, pow_two] <;> simp_all [eq_comm, pow_two]
  tauto

end

/-- Fourth-integrable coordinate errors have square-integrable products. -/
theorem independent_error_product_memLp_two [MeasurableSpace Ω]
    (μ : Measure Ω) (ε : ι → Ω → ℝ)
    (hε : ∀ i, MemLp (ε i) 4 μ) (i j : ι) :
    MemLp (fun ω => ε i ω * ε j ω) 2 μ := by
  letI : ENNReal.HolderTriple 4 4 2 := ⟨by
    rw [← two_mul, show (4 : ENNReal) = 2 * 2 by norm_num,
      ENNReal.mul_inv (by simp) (by simp), ← mul_assoc,
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]⟩
  exact (hε i).mul (r := 2) (hε j)

section
variable [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- The actual independent-error covariance rule for quadratic
monomials.  Its diagonal coefficient is the variance of the squared
coordinate error, and both crossing pairs contribute `V²`. -/
theorem independent_error_product_covariance
    (ε : ι → Ω → ℝ) (hind : iIndepFun ε μ) (hε : ∀ i, MemLp (ε i) 4 μ)
    (hmean : ∀ i, (∫ ω, ε i ω ∂μ) = 0) (V : ℝ)
    (hsecond : ∀ i, (∫ ω, ε i ω ^ 2 ∂μ) = V) :
    HasProjectionProductCovariance μ (fun ω i => ε i ω) V (fun i => (∫ ω, ε i ω ^ 4 ∂μ) - V ^ 2) := by
  rintro ⟨i, j⟩ ⟨k, l⟩
  simp only [Prod.mk.injEq, Prod.swap_prod_mk]
  have htwo (i : ι) : MemLp (ε i) 2 μ := (hε i).mono_exponent (by norm_num)
  have hcov := projection_coordinate_covariance μ (fun ω i => ε i ω) V htwo hind hmean hsecond
  rw [covariance_eq_sub (independent_error_product_memLp_two μ ε hε i j)
    (independent_error_product_memLp_two μ ε hε k l)]
  simp only [Pi.mul_apply]
  simp_rw [← mul_assoc]
  rw [independent_error_fourth_product μ ε hind (fun i => (hε i).aestronglyMeasurable)
    hmean V hsecond i j k l, hcov i j, hcov k l]
  split_ifs <;> grind

/-- Full conditional residual-estimator risk inequality from actual
independent centered errors with bounded fourth moments.  All primitive
product covariance rules in the earlier variance theorem are discharged. -/
theorem independent_projection_estimator_mse_bound (A : Matrix ι ι ℝ)
    (hsym : Aᵀ = A) (hidem : A * A = A) (hd : 0 < A.trace)
    (f : ι → ℝ) (ε : ι → Ω → ℝ) (V C₄ : ℝ)
    (hε : ∀ i, MemLp (ε i) 4 μ) (hind : iIndepFun ε μ)
    (hmean : ∀ i, (∫ ω, ε i ω ∂μ) = 0)
    (hsecond : ∀ i, (∫ ω, ε i ω ^ 2 ∂μ) = V)
    (hfourth : ∀ i, (∫ ω, ε i ω ^ 4 ∂μ) ≤ C₄) :
    (∫ ω, (projectionEstimator A (f + fun i => ε i ω) - V) ^ 2 ∂μ) ≤
      (2 * max C₄ (2 * V ^ 2) * A.trace + 8 * V * projectionEnergy (A *ᵥ f)) / A.trace ^ 2 +
        (projectionEnergy (A *ᵥ f) / A.trace) ^ 2 := by
  have htwo (i : ι) : MemLp (ε i) 2 μ := (hε i).mono_exponent (by norm_num)
  apply projection_estimator_mse_bound μ A hsym hidem hd f (fun ω i => ε i ω)
    V (max C₄ (2 * V ^ 2)) (fun i => (∫ ω, ε i ω ^ 4 ∂μ) - V ^ 2)
    htwo hmean (projection_coordinate_covariance μ (fun ω i => ε i ω) V htwo hind hmean hsecond)
    (independent_error_product_memLp_two μ ε hε)
    (independent_error_product_covariance μ ε hind hε hmean V hsecond)
  · exact fun i => (sub_le_self _ (sq_nonneg V)).trans ((hfourth i).trans (le_max_left ..))
  · exact le_max_right ..

end

end

end NearlyMinimax
