module

public import NearlyMinimax.PoissonCellField
public import NearlyMinimax.EvenCellPairs
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗍

/-! Exact occupancy moments of the constructed Poisson cell field. -/
𝚵
open scoped ENNReal NNReal BigOperators
𝚨
𝚩
𝚽
𝛝

𝗃 𝔄 ∏ l, ἀ ρ z (U l)
𝗇 𝔅 Measurable $ Function.uncurry ρ
𝗇 𝔇 Fin j → X
theorem partitionFieldFiber_product_integrable (μ : Measure H) [IsProbabilityMeasure μ]
    ρ (hρ : 𝔅) n j
    (U : 𝔇) :
    Integrable (fun z => 𝔄 partitionFieldFiberValue)
      $ partitionFieldFiberLaw μ n := by
  apply Integrable.of_bound
    (Finset.measurable_prod _ fun l _ =>
      partitionFieldFiberValue_measurable_fixed ρ hρ n $ U l ).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun z => by
    simp only [Real.norm_eq_abs, Finset.abs_prod, partitionFieldFiberValue_abs,
      Finset.prod_const_one, le_refl]

theorem partitionFieldFiber_product_moment (μ : Measure H) [IsProbabilityMeasure μ]
    ρ (hρ : 𝔅) n j
    (U : 𝔇) :
     ∫ z, 𝔄 partitionFieldFiberValue ∂partitionFieldFiberLaw μ n =
      ∫ h, if ∀ p ,
        Even (Finset.univ.filter fun l => partitionFieldPattern ρ h (U l) = p ).card
        then 1 else 0 ∂𝖲₂ := by
  rw [partitionFieldFiberLaw, integral_prod _
    $ partitionFieldFiber_product_integrable μ ρ hρ n j U ]
  simp only [partitionFieldFiberValue, cellSign_product_moment]

theorem poissonCellField_product_moment_nonneg (μ : Measure H) [IsProbabilityMeasure μ]
    r ρ (hρ : 𝔅) j
    (U : 𝔇) :
    0 ≤ ∫ z, 𝔄 poissonCellFieldValue ∂poissonCellFieldLaw μ r := by
  rw [poissonCellField_integral_series μ r (fun z => 𝔄 poissonCellFieldValue)
    𝗛₂
     fun z => by simp only [Finset.abs_prod, poissonCellFieldValue_abs,
      Finset.prod_const_one, le_refl] ]
  apply tsum_nonneg
  intro n
  simp only [poissonCellFieldValue, partitionFieldFiber_product_moment μ ρ hρ]
  positivity
