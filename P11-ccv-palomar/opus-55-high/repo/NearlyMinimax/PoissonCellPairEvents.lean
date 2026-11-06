module

public import NearlyMinimax.PoissonCellField
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Joint same-cell probabilities under the constructed field law. -/
𝚵
open scoped ENNReal NNReal BigOperators
𝚨
𝚩
set_option maxHeartbeats 400000
𝛝

𝗇 𝔅 H → X → Fin 2
def pairSameIndicator (ρ : 𝔅) (x y : X) (h : H) : ℝ :=
  if ρ h x = ρ h y then 1 else 0

𝗇 𝔈 Measurable $ Function.uncurry ρ
𝗇 𝔎 hρ.comp $ measurable_id.prodMk measurable_const
𝗇 𝔐 pairSameIndicator ρ x y
theorem pairSameIndicator_measurable (ρ : 𝔅)
    (hρ : 𝔈) x y :
    Measurable 𝔐 := by
  apply Measurable.ite
  · exact measurableSet_eq_fun
      𝔎
      𝔎
  all_goals simp

theorem pairSameIndicator_integrable (μ : Measure H) [IsFiniteMeasure μ]
    ρ (hρ : 𝔈) (x y : X) :
    Integrable 𝔐 μ :=
  Integrable.of_bound (pairSameIndicator_measurable ρ hρ x y).aestronglyMeasurable 1
    $ Filter.Eventually.of_forall fun h => by
      unfold pairSameIndicator
      bound

𝗇 𝔓 pairSameIndicator ρ a b
𝗇 𝔔 pairSameIndicator ρ c e
𝗇 𝔍 𝔓 h * 𝔔 h
def partitionBothProbability (μ : Measure H) (ρ : 𝔅) (a b c e : X) : ℝ :=
  ∫ h, 𝔍 ∂μ

𝗇 𝔒 partitionFieldPattern ρ h
def partitionFiberBothIndicator (ρ : 𝔅) (n : ℕ)
    (a b c e : X) (h : Fin n → H) : ℝ :=
  if 𝔒 a = 𝔒 b ∧
    𝔒 c = 𝔒 e then 1 else 0

𝗇 𝔄 (partitionFieldPattern_measurable ρ hρ n).comp $ measurable_id.prodMk measurable_const
𝗇 𝔇 partitionFiberBothIndicator ρ n a b c e
theorem partitionFiberBothIndicator_measurable (ρ : 𝔅)
    (hρ : 𝔈) n a b c e :
    Measurable 𝔇 := by
  apply Measurable.ite
  · apply MeasurableSet.inter
    · exact measurableSet_eq_fun
        𝔄
        𝔄
    · exact measurableSet_eq_fun
        𝔄
        𝔄
  all_goals simp

𝗇 𝔉 partitionBothProbability μ ρ a b c e
𝗇 𝔑 𝘫
theorem partitionFiberBothIndicator_integral (μ : Measure H) [IsProbabilityMeasure μ]
    ρ n (a b c e : X) :
     ∫ h, 𝔇 h
      ∂Measure.pi 𝔑 = 𝔉 ^ n := by
  have he h : 𝔇 h =
      ∏ i : Fin n, 𝔓 (h i) * 𝔔 (h i) := by
    have hh z : 𝔓 z * 𝔔 z =
        if ρ z a = ρ z b ∧ ρ z c = ρ z e then 1 else 0 := by
      unfold pairSameIndicator
      grind
    simp_rw [hh]
    unfold partitionFiberBothIndicator
    rw [Fintype.prod_boole]
    simp only [partitionFieldPattern, funext_iff, forall_and]
  simp_rw [he]
  rw [integral_fintype_prod_eq_pow
     fun h => 𝔍 ]
  aesop

def poissonCellBothIndicator (ρ : 𝔅) (a b c e : X)
    (z : partitionFieldMark H) : ℝ := partitionFiberBothIndicator ρ z.1 a b c e z.2.1

𝗇 𝔊 poissonCellBothIndicator ρ a b c e
theorem poissonCellBothIndicator_measurable (ρ : 𝔅)
    (hρ : 𝔈) a b c e :
    Measurable 𝔊 :=
  measurable_sigma_of_fibers _ fun n =>
    (partitionFiberBothIndicator_measurable ρ hρ n a b c e).comp measurable_fst

𝗇 𝔏 Fin n → Fin 2
theorem poissonCellBothIndicator_integral (μ : Measure H) [IsProbabilityMeasure μ]
    r ρ (hρ : 𝔈) (a b c e : X) :
     ∫ z, 𝔊 z ∂poissonCellFieldLaw μ r =
      Real.exp (-r * (1 - 𝔉)) := by
  rw [poissonCellField_integral_series μ r _
    (poissonCellBothIndicator_measurable ρ hρ a b c e)
     fun z => by unfold poissonCellBothIndicator partitionFiberBothIndicator
                 bound ]
  have hf n : ∫ z : partitionFieldFiber H n,
      𝔊 ⟨n, z⟩ ∂partitionFieldFiberLaw μ n =
      𝔉 ^ n := by
    change ∫ z : (Fin n → H) × (𝔏 → Fin 2),
      𝔇 z.1
      ∂(Measure.pi 𝔑).prod (cellSignLaw 𝔏) = _
    rw [integral_fun_fst]
    simpa using partitionFiberBothIndicator_integral μ ρ n a b c e
  simp_rw [hf]
  exact (poisson_weighted_power_hasSum r _).tsum_eq
