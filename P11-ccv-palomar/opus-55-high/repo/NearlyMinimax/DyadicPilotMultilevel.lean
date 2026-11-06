module

public import NearlyMinimax.DyadicPilotWeakTests
public import NearlyMinimax.PilotMultilevelCore
public import NearlyMinimax.PilotSeriesEnvelope
public import NearlyMinimax.DyadicPilotFieldMeasurability
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Actual multilevel pilot errors, their mean and pointwise energy, and
their universal covariance under the original pair design measure. -/
𝚵
𝚳
𝚨
𝚭
𝚩

𝗇 𝔑 𝙌
𝗇 𝔒 𝙩
𝗃 𝔢 ἀ C θ
𝗇 𝔘 𝔢 dyadicPilotErrorField n j.val y $ m j.val
𝗇 𝔚 Fin 𝗯
def dyadicMultilevelErrorField (C : ModelConstants d) (θ : RegressionParameter d)
    (n J : ℕ) (y : ℝ) (m : 𝙦₁) (z : 𝔑)
    (w : 𝔒) : ℝ :=
  ∑ j : 𝔚, 𝔘 z w

def dyadicMultilevelBudget (H : ℝ) (J L : ℕ) : ℝ :=
   (𝙉 ^ L)⁻¹ ^ 2 * (𝙉 ^ J) ^ 2 * H

𝗇 𝔅 𝘻₁
theorem dyadicPilotRowCap_square d ℓ j L D :
    (dyadicPilotRowCap d ℓ j L * D) ^ 2 =
      (𝚃 * D) ^ 2 * d *
         𝔅⁻¹ ^ 2 * 𝗜 ^ 2 := by
  simp only [dyadicPilotRowCap, mul_pow, Real.sq_sqrt $ Nat.cast_nonneg d ]
  ring

𝗇 𝔇 Nonempty 𝘘
𝗇 𝔊 sampleLaw θ n
𝗇 𝔍 m + 𝗣 + 1
𝗇 𝔟 𝔢 dyadicPilotErrorField n j y m t
𝗇 𝔎 𝔟 (x, z)
𝗇 𝔓 𝔢 Admissible
𝗃 𝔛 𝔢 ἀ hθ n
𝗃 𝔣 ∫ t, ἀ ∂𝔊 = 0
𝗃 𝔡 MemLp (fun t => ἀ) 2 𝔊
theorem dyadicPilotErrorField_point_moment_facts (C : ModelConstants d)
    [𝔇] θ (hθ : 𝔓)
    n j x (hx : 𝗌) z
    y m (hdegree : 𝔍 ≤ n) :
    𝔡 𝔎 ∧
      𝔣 𝔎 := by
  let := 𝔛 sampleLaw_isProbability
  obtain ⟨hL2, hmean⟩ := 𝔛 dyadicPolynomialPilot_moment_facts j x hx y m
    (dyadicPilotRow j x z) hdegree
  refine ⟨hL2.sub $ memLp_const _ , ?_⟩
  unfold dyadicPilotErrorField
  rw [integral_sub (hL2.integrable 𝖠₄ ) $ integrable_const _ , hmean]
  simp

𝗇 𝔄 ∀ j : 𝔚, m j.val + 𝗣 + 1 ≤ n
𝗇 𝔙 𝔢 dyadicMultilevelErrorField n J y m
𝗇 𝔏 𝔙 t (x, z)
𝗇 𝔐 memLp_finsetSum _ fun j _ => (hf j).1
theorem dyadicMultilevelErrorField_point_moment_facts (C : ModelConstants d)
    [𝔇] θ (hθ : 𝔓)
    n J x (hx : 𝗌) z
    y m
    (hdegree : 𝔄) :
    𝔡 𝔏 ∧
      𝔣 𝔏 := by
  let := 𝔛 sampleLaw_isProbability
  have hf j := 𝔛 dyadicPilotErrorField_point_moment_facts j.val x hx z y
    (m j.val) $ hdegree j
  refine ⟨𝔐, ?_⟩
  unfold dyadicMultilevelErrorField
  rw [integral_finsetSum Finset.univ fun j _ => (hf j).1.integrable 𝖠₄ ]
  simp_all

𝗇 𝔉 fun w => ν w * 𝔟 w
𝗇 𝔔 2 ^ L
𝗇 𝔗 regularPairDesignMeasure θ 𝔅
𝗇 𝔜 dyadicPilotRow j w.1 w.2
𝗇 𝔞 𝗙₁
theorem dyadicPilotErrorField_weighted_integrable (C : ModelConstants d)
    [𝔇] θ (hθ : 𝔓)
    n j L (hj : j ≤ L) y (hy : |y| ≤ C.holderBound) m
    (hdegree : 𝔍 ≤ n)
    ν
    (hν : MemLp ν 2 $ 𝔗 𝖠₃ )
    t :
    Integrable 𝔉
      $ 𝔗 $ by positivity := by
  let M := regularPairDesignMeasure θ 𝔔 𝖠₃
  let := 𝔢 regularPairDesignMeasure_isFinite hθ 𝔔 𝖠₃
  let R := 𝔍
  let H (w : 𝔒) (r : Fin R) :=
    𝔢 dyadicIncrementKernel j w.1 y m 𝔜 𝔞
  let X i (z : 𝔑) :=
    incrementGlobalVector (ℓ := C.order) j (z i) - 𝚆₁
  have hrow := dyadicPilotRow_pair_cap (ℓ := C.order) C θ hθ j L hj
  have hH (r : Fin R) :=
    𝔢 dyadicIncrementKernel_weighted_integrable hθ j y hy m 𝔞 _
      (dyadicPilotRow_field_measurable j) M (dyadicPilotRowCap d C.order j L)
      (dyadicPilotRowCap_nonneg ..) ((𝔢 regularPairDesignMeasure_cube_ae hθ 𝔔 𝖠₃ ).mono fun w hw => hw.1 ) hrow ν hν
  have hi := integrable_finsetSum Finset.univ fun r _ =>
    FieldLiftCovariance.weighted_kernel_statistic_integrable X ν (fun w => H w r) (hH r) t
  have heq : 𝔉 =
       fun w => ∑ r : Fin R, ν w * LiftL2.kernelStatistic (H w r) X t := by
    funext w
    unfold dyadicPilotErrorField
    rw [← 𝔛 dyadicPolynomialPilot_centered_global j w.1 y m
      𝔜 hdegree t]
    simp only [LiftL2.centeredKernelExpansion, zero_add, Finset.mul_sum]
    rfl
  grind

𝗇 𝔈 ν w * 𝔙 t w
𝗇 𝔖 (Nat.le_of_lt_succ j.isLt).trans hJL
𝗃 𝔠 𝔛 ἀ j.val L 𝔖 y hy (m j.val) (hdegree j) ν hν
theorem dyadicMultilevelErrorField_test_integral_sum (C : ModelConstants d)
    [𝔇] θ (hθ : 𝔓)
    n J L (hJL : 𝚗₂) y (hy : |y| ≤ C.holderBound) m
    (hdegree : 𝔄)
    ν
    (hν : MemLp ν 2 $ 𝔗 𝖠₃ )
    t :
     ∫ w, 𝔈
      ∂𝔗  𝖠₃  =
    ∑ j : 𝔚, ∫ w, ν w * 𝔘 t w
      ∂𝔗  𝖠₃  := by
  unfold dyadicMultilevelErrorField
  simp_rw [Finset.mul_sum]
  exact integral_finsetSum Finset.univ fun j _ =>
    𝔠 dyadicPilotErrorField_weighted_integrable t

theorem dyadicMultilevelErrorField_test_moment_facts (C : ModelConstants d)
    [𝔇] θ (hθ : 𝔓)
    n J L (hJL : 𝚗₂) y (hy : |y| ≤ C.holderBound) m
    (hdegree : 𝔄)
    ν
    (hν : MemLp ν 2 $ 𝔗 𝖠₃ ) :
    MemLp (fun t => ∫ w, 𝔈
      ∂𝔗  𝖠₃ ) 2 𝔊 ∧
     ∫ t, ∫ w, 𝔈
      ∂𝔗  𝖠₃  ∂𝔊 = 0 := by
  let := 𝔛 sampleLaw_isProbability
  have hf j := 𝔠 dyadicPilotErrorField_test_moment_facts
  simp_rw [𝔛 dyadicMultilevelErrorField_test_integral_sum J L hJL y hy m hdegree ν hν]
  refine ⟨𝔐, ?_⟩
  rw [integral_finsetSum Finset.univ fun j _ => (hf j).1.integrable 𝖠₄ ]
  simp_all

theorem dyadicMultilevelErrorField_joint_measurable (C : ModelConstants d)
    [𝔇] (θ : RegressionParameter d) (hθ : 𝔓)
    (n J : ℕ) (y : ℝ) (m : 𝙦₁)
    (hdegree : 𝔄) :
    Measurable fun t : 𝔑 × 𝔒 =>
      𝔙 t.1 t.2 := by
  have hm := Finset.measurable_sum Finset.univ fun j _ =>
    𝔛 dyadicPolynomialPilot_centered_field_measurable j.val y (m j.val)
      (fun w => dyadicPilotRow j.val w.1 w.2) (dyadicPilotRow_field_measurable j.val) $ hdegree j
  assumption
