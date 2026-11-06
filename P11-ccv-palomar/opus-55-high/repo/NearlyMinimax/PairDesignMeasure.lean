module

public import NearlyMinimax.FinitePartitionMoments
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! The actual weighted same-cell design-pair measure. -/
𝚫
𝚳
𝚨
𝚩

𝗃 𝔔 ∫ z, f z ∂ἀ
𝗃 𝔖 sameLabelKernel ἀ z • f z
section Partition
variable {X I : Type*} [MeasurableSpace X] [Fintype I] [MeasurableSpace I]
  [MeasurableSingletonClass I] [MeasurableEq I]
variable (μ : Measure X) [IsProbabilityMeasure μ] (label : X → I)

𝗇 𝔅 𝚌₁
𝗇 𝔊 X × X
def partitionPairMeasure (weight : ℝ) : Measure 𝔊 :=
  ENNReal.ofReal weight • (μ.prod μ).restrict {z | 𝔅}

𝗇 𝔍 partitionPairMeasure μ label weight
instance partitionPairMeasure_isFinite (weight : ℝ) :
    IsFiniteMeasure 𝔍 := ((μ.prod μ).restrict {z | 𝔅}).smul_finite ENNReal.ofReal_ne_top

theorem partitionPairMeasure_integral (hlabel : Measurable label)
    (hw : 0 ≤ weight) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : 𝔊 → E) :
    𝔔 𝔍 =
      weight • ∫ z, 𝔖 label ∂μ.prod μ := by
  have hC : MeasurableSet {z : 𝔊 | 𝔅} :=
    𝗝₁
  have he : (fun z => 𝔖 label) =
      {z : 𝔊 | 𝔅}.indicator f := by
    funext z
    by_cases hz : 𝔅
    · simp [sameLabelKernel, hz]
    · simp [sameLabelKernel, hz]
  rw [partitionPairMeasure, integral_smul_measure, ENNReal.toReal_ofReal hw, he,
    integral_indicator hC]

theorem partitionPairMeasure_real_univ (hlabel : Measurable label)
    (hw : 0 ≤ weight) :
    (𝔍).real univ =
      weight * ∑ i : I, μ.real (label ⁻¹' {i}) ^ 2 := by
  have hi := partitionPairMeasure_integral μ label hlabel hw fun _ => 𝙠
  simp at hi
  rwa [sameLabelKernel_integral μ label hlabel] at hi

end Partition

𝗇 𝔄 𝘯
𝗇 𝔇 𝙦 ^ d
𝗇 𝔎 𝖱
𝗇 𝔐 𝙩
def regularPairDesignMeasure (θ : RegressionParameter d) (k : ℕ) (hk : 𝖰) :
    Measure 𝔐 :=
  ENNReal.ofReal 𝔇 • (𝔎).restrict
    {z | 𝔄 z.1 = 𝔄 z.2}

𝗇 𝔈 𝗪₁
𝗇 𝔑 𝘪₁
𝗃 𝔗 ἀ (designLaw θ) 𝔄
theorem regularPairDesignMeasure_isFinite C
    (θ : RegressionParameter d) (hθ : 𝙟) k hk :
    IsFiniteMeasure 𝔈 := by
  let := 𝔑
  change IsFiniteMeasure $ 𝔗 partitionPairMeasure 𝗋
  infer_instance

𝗇 𝔉 pow_nonneg (Nat.cast_nonneg k) d
𝗇 𝔒 regular_grid_cell_measurable k hk
theorem regularPairDesignMeasure_integral (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : 𝙟) (k : ℕ) (hk : 𝖰)
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : 𝔐 → E) :
    𝔔 𝔈 =
      𝔇 • ∫ z, 𝔖 𝔄
        ∂𝔎 := by
  let := 𝔑
  exact 𝔗 partitionPairMeasure_integral
    𝔒 𝔉 f

section

variable (C)
    (θ : RegressionParameter d)
    (hθ : 𝙟)
    (k)
    (hk)

include hθ k hk

𝗇 𝔏 (𝔈).real univ
theorem regularPairDesignMeasure_mass :
    𝔏 =
      𝗋 * 𝘬₁ := by
  let := 𝔑
  exact 𝔗 partitionPairMeasure_real_univ
    𝔒 𝔉

𝗃 𝔓 ἀ C θ hθ k hk
theorem regularPairDesignMeasure_mass_bounds :
    1 ≤ 𝔏 ∧
      𝔏 ≤ C.densityUpper := by
  rw [𝔓 regularPairDesignMeasure_mass]
  have hkp : 0 < 𝔇 := pow_pos (by exact_mod_cast hk) d
  constructor
  · have h := mul_le_mul_of_nonneg_left 𝔓 regularGridCollisionMass_lower hkp.le
    grind
  · simpa [hkp.ne', mul_comm, mul_div_cancel₀] using mul_le_mul_of_nonneg_left 𝔓 regularGridCollisionMass_upper hkp.le
