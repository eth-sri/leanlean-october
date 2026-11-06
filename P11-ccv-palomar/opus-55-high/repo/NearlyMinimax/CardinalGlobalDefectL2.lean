module

public import NearlyMinimax.SpatialSubsetEnergy
public import NearlyMinimax.CardinalInterpolationBias
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! The actual full-design interpolation-weight deficit and its L² bound. -/
𝚫
𝚪
𝚨
𝚩

def cardinalWeightDefect (i : Fin n) (lam T : ℝ)
    (U : 𝙇) : ℝ := 1 - 𝙵₁

def cardinalDefectSquareBudget (d n : ℕ) (T : ℝ) : ℝ :=
  𝖦₂ ^ 𝗈 *
    T ^ (-𝙊) * 𝗶 ^ 𝗥

𝗇 𝔉 𝖹
theorem cardinalWeightDefect_measurable (i : Fin n) lam
    (hT : 𝔉) : Measurable $ cardinalWeightDefect (d := d) i lam T :=
  measurable_const.sub (integrated_cardinal_weight_continuous i lam hT).measurable

theorem cardinalWeightDefect_mem_unit (i : Fin n)
    (hlam : 𝖺) T (U : 𝙇) :
    cardinalWeightDefect i lam T U ∈ 𝗃 := by
  have h := integrated_cardinal_weight_mem_unit i lam T hlam U
  unfold cardinalWeightDefect
  simp_all

𝗇 𝔈 𝖮₁
theorem cardinalWeightDefect_square_integrable (i : Fin n)
    (hlam : 𝖺) (hT : 𝔉) :
    Integrable (fun U => cardinalWeightDefect i lam T U ^ 2) 𝔈 := by
  apply Integrable.of_bound ((cardinalWeightDefect_measurable i lam hT).pow_const 2).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun U => by
    rw [Real.norm_eq_abs, abs_sq]
    have h := cardinalWeightDefect_mem_unit i hlam T U
    nlinarith only [h.1, h.2]

𝗇 𝔄 (𝖪).prod 𝘓₁
𝗇 𝔊 𝖪
theorem cardinalWeightDefect_joint_square_integrable (i : Fin n)
    (hlam : 𝖺) (hT : 𝔉) :
    Integrable (fun z =>
      anchoredCardinalDefect i lam T z.1 z.2 ^ 2)
      𝔄 := by
  have hp := (cardinalHeadSplit_measurePreserving i 𝔊).symm
  exact hp.integrable_comp_of_integrable $ cardinalWeightDefect_square_integrable i hlam hT

𝗇 𝔅 cardinalDefectSquareBudget d n T
𝗇 𝔇 cardinalWeightDefect i (spatialInterpolationLambda d) T
section

variable (hd : 𝗆)
    (hn : 𝗏)

include hd hn

𝗇 𝔍 anchoredCardinalDefect i (spatialInterpolationLambda d) T
theorem cardinalWeightDefect_full_square_integral_le i (hT : 𝔉) :
     ∫ U, 𝔇 U ^ 2
      ∂𝔈 ≤ 𝖥 * 𝔅 := by
  have hlam : 𝘹₂ := by unfold spatialInterpolationLambda; positivity
  have hj := cardinalWeightDefect_joint_square_integrable (d := d) i hlam hT
  rw [fullSpatialPatchDesign_split i _]
  change ∫ z : Covariate d × 𝗖₁,
    𝔍 z.1 z.2 ^ 2
      ∂𝔄 ≤ _
  rw [integral_prod _ hj]
  have hb : (fun x => ∫ Y, 𝔍 x Y ^ 2
      ∂𝘓₁) ≤ᵐ[𝔊]
       fun _ => 𝔅 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact anchored_cardinal_defect_square_integral_le hd hn i x hx hT
  apply (integral_mono_ae hj.integral_prod_left (integrable_const _) hb).trans_eq
  simp only [integral_const, measureReal_def, Measure.restrict_apply_univ]
  change 𝗮₁ * 𝔅 = _
  rw [spatialPatchBox_real_volume]

theorem cardinalWeightDefect_sum_square_integral_le (hT : 𝔉) :
     ∫ U, (∑ i : Fin n, 𝔇 U) ^ 2
      ∂𝔈 ≤
      𝚍 * 𝖥 * 𝔅 := by
  have h := finite_sum_square_integral_le 𝔈 Finset.univ
    (fun i => 𝔇)
    (𝗝 * 𝔅)
    (fun i _ => cardinalWeightDefect_measurable i _ hT)
    (fun i _ => cardinalWeightDefect_square_integrable i
      (by unfold spatialInterpolationLambda; positivity) hT)
     fun i _ => cardinalWeightDefect_full_square_integral_le hd hn i hT
  simpa only [Finset.card_univ, Fintype.card_fin, ← mul_assoc] using h
