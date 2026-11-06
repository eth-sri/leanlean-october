module

public import NearlyMinimax.Projection
public import RoughRegime.Macro
public import RoughRegime.Notation


public section

open Matrix MeasureTheory ProbabilityTheory


𝚨

𝗇 𝔄 ε i ω
𝗇 𝔏 fun i => 𝔄
𝗇 𝔑 ∀ i, AEStronglyMeasurable (ε i) μ
𝗇 𝔔 iIndepFun ε μ
𝗇 𝔖 𝔄 ^ l.count i
/-- Independence factors arbitrary finite lists of coordinate errors,
including repeated indices grouped into their multiplicities. -/
theorem independent_error_list_moment [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ε : ι → 𝘄) (hind : 𝔔)
    (hmeas : 𝔑) (l : List ι) :
     ∫ ω, (l.map 𝔏).prod ∂μ =
      ∏ i ∈ l.toFinset, ∫ ω, 𝔖 ∂μ := by
  have hid ω : (l.map 𝔏).prod = ∏ i : ι, 𝔖 := by
    rw [Finset.prod_list_map_count]
    apply Finset.prod_subset $ Finset.subset_univ l.toFinset
    intro i hi hin
    rw [List.count_eq_zero.mpr $ by simpa using hin , pow_zero]
  simp_rw [hid]
  have hiPow : iIndepFun (fun i ω => 𝔖) μ :=
    hind.comp (fun i x => x ^ l.count i) fun i => measurable_id.pow_const _
  rw [hiPow.integral_fun_prod_eq_prod_integral fun i => (hmeas i).pow _ ]
  symm
  apply Finset.prod_subset $ Finset.subset_univ l.toFinset
  intro i hi hin
  simp only [List.count_eq_zero.mpr $ by simpa using hin ]
  simp

𝗇 𝔅 V ^ 2
𝗇 𝔈 ∫ ω, 𝔄 ^ 4 ∂μ
𝗇 𝔉 ∀ i, ∫ ω, 𝔄 ^ 2 ∂μ = V
𝗇 𝔊 ∀ i, ∫ ω, 𝔄 ∂μ = 0
𝗇 𝔗 i = k
/-- The four-coordinate moment rule behind the variance of a quadratic
form, derived from actual independence and centered errors. -/
theorem independent_error_fourth_product [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    ε (hind : 𝔔)
    (hmeas : 𝔑)
    (hmean : 𝔊) (V : ℝ)
    (hsecond : 𝔉) (i j k l : ι) :
     ∫ ω, 𝔄 * ε j ω * ε k ω * ε l ω ∂μ =
      if i = j then
        if k = l then if 𝔗 then 𝔈 else 𝔅 else 0
      else if 𝔗 ∧ j = l then 𝔅
      else if 𝚛₁ ∧ j = k then 𝔅 else 0 := by
  have he := independent_error_list_moment μ ε hind hmeas [i, j, k, l]
  simp at he
  simp_rw [← mul_assoc] at he
  by_cases hij : i = j <;> by_cases hik : 𝔗 <;> by_cases hil : 𝚛₁ <;>
    by_cases hjk : j = k <;> by_cases hjl : j = l <;> by_cases hkl : k = l <;>
    subst_vars <;>
    simp_all [pow_two] <;>
    simp_all [eq_comm, pow_two]
  bound

𝗇 𝔇 𝗜₂
𝗇 𝔎 fun ω => 𝔄 * ε j ω
/-- Fourth-integrable coordinate errors have square-integrable products. -/
theorem independent_error_product_memLp_two [MeasurableSpace Ω]
    (μ : Measure Ω) (ε : ι → 𝘄)
    (hε : 𝔇) i j :
    MemLp 𝔎 2 μ := by
  letI : ENNReal.HolderTriple 4 4 2 := ⟨by
    rw [← two_mul, show (4 : ENNReal) = 2 * 2 by norm_num,
      ENNReal.mul_inv  𝖢₄  𝖢₄ , ← mul_assoc,
      ENNReal.mul_inv_cancel  𝖠₄  𝖠₄ , one_mul]⟩
  convert (hε j).mul (r := 2) $ hε i using 1
  funext ω
  simp [mul_comm]

𝗇 𝔙 fun ω i => 𝔄
𝗇 𝔍 projection_coordinate_covariance μ 𝔙 V htwo hind hmean hsecond
𝗇 𝔒 independent_error_product_memLp_two μ ε hε
𝗇 𝔘 MemLp (ε i) 2 μ
/-- The actual independent-error covariance rule for quadratic
monomials. Its diagonal coefficient is the variance of the squared
coordinate error, and both crossing pairs contribute `V²`. -/
theorem independent_error_product_covariance [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    ε (hind : 𝔔) (hε : 𝔇)
    (hmean : 𝔊) V
    (hsecond : 𝔉) (i j k l : ι) :
    covariance 𝔎 (fun ω => ε k ω * ε l ω) μ =
      (if 𝔗 ∧ j = l then
         if i = j then 𝔈 - 𝔅 else 𝔅 else 0) +
       if 𝚛₁ ∧ j = k ∧ 𝘚₁ then 𝔅 else 0 := by
  have htwo i : 𝔘 := (hε i).mono_exponent 𝖠₄
  have hcov := 𝔍
  rw [covariance_eq_sub (𝔒 i j)
    $ 𝔒 k l ]
  simp
  simp_rw [← mul_assoc]
  rw [independent_error_fourth_product μ ε hind (fun i => (hε i).aestronglyMeasurable)
    hmean V hsecond i j k l, hcov i j, hcov k l]
  grind

𝗇 𝔐 2 * 𝔅
𝗇 𝔓 A *ᵥ f
/-- Full conditional residual-estimator risk inequality from actual
independent centered errors with bounded fourth moments. All primitive
product covariance rules in the earlier variance theorem are discharged. -/
theorem independent_projection_estimator_mse_bound
    [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] A
    (hsym : Aᵀ = A) (hidem : A * A = A) (hd : 0 < A.trace)
    (f : 𝙛) ε V C₄
    (hε : 𝔇) (hind : 𝔔)
    (hmean : 𝔊)
    (hsecond : 𝔉)
    (hfourth : ∀ i, 𝔈 ≤ C₄) :
     ∫ ω, (projectionEstimator A (f + 𝔏) - V) ^ 2 ∂μ ≤
      (2 * max C₄ 𝔐 * A.trace + 8 * V * projectionEnergy 𝔓) / A.trace ^ 2 +
        (projectionEnergy 𝔓 / A.trace) ^ 2 := by
  have htwo i : 𝔘 := (hε i).mono_exponent 𝖠₄
  apply projection_estimator_mse_bound μ A hsym hidem hd f 𝔙
    V (max C₄ 𝔐) (fun i => 𝔈 - 𝔅)
    htwo hmean 𝔍
    𝔒
    $ independent_error_product_covariance μ ε hind hε hmean V hsecond
  · intro i
    have hf := hfourth i
    have hmax := le_max_left C₄ 𝔐
    nlinarith
  simp
